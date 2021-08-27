from typing import Dict, Optional, cast

import braket.circuits
import quasar
from icontract.errors import ViolationError
from pyrsistent import pset
from pyrsistent.typing import PSet
from toolz.functoolz import thread_first

from qcware_transpile import TranslationException
from qcware_transpile.circuits import Circuit
from qcware_transpile.dialects import braket as braket_dialect
from qcware_transpile.dialects import quasar as quasar_dialect
from qcware_transpile.matching import (
    TranslationRule,
    TranslationSet,
    best_rule_for_instruction_set,
    rule_matches_instruction_set,
    simple_translate,
    trivial_rules,
    untranslatable_instructions,
    untranslated_gates,
)


# for an Rx gate
# as per https://github.com/aws/amazon-braket-sdk-python/blob/main/src/braket/circuits/gates.py#L422
#  def to_matrix(self) -> np.ndarray:
#        cos = np.cos(self.angle / 2)
#        sin = np.sin(self.angle / 2)
#        return np.array([[cos, -1j * sin], [-1j * sin, cos]], dtype=complex)
# vs quasar: https://github.com/qcware/quasar/blob/master/quasar/circuit.py#L226
#        c = np.cos(theta)
#        s = np.sin(theta)
# so we must double angles from quasar to braket
def double_angle(theta):
    return 2 * theta


def translation_set(allowed_instructions: Optional[PSet[str]] = None) -> TranslationSet:
    """Creates a translation set from quasar to braket.

    There's an irritation: not all backends support the same
    instructions, so we have to filter.  You can actually get a list
    of supported operations with

    device = AwsDevice(arn)
    print(device.properties.dict()['action']['braket.ir.jacqd.program']['supportedOperations'])

    ...this will obligingly give you a list of all quantum gates supported by the device...
    ... IN LOWERCASE ONLY.

    So the reason this is fun is that we should be able to easily eliminate translations, but
    this is problematic because they're encoded with upper and lower case.  So we'll do the
    expedient thing and compare them that way.
    """
    trivial_gates = {
        ("I", "I"),
        ("H", "H"),
        ("X", "X"),
        ("Y", "Y"),
        ("Z", "Z"),
        ("S", "S"),
        ("ST", "Si"),
        ("T", "T"),
        ("TT", "Ti"),
        ("CX", "CNot"),
        ("CY", "CY"),
        ("CZ", "CZ"),
        ("CCX", "CCNot"),
        ("u1", "PhaseShift"),
        ("SWAP", "Swap"),
        ("CSWAP", "CSwap"),
        ("Rx", "Rx", double_angle),
        ("Ry", "Ry", double_angle),
        ("Rz", "Rz", double_angle),
    }

    quasar_d = quasar_dialect.dialect()
    braket_d = braket_dialect.dialect()

    rbs_rules = [
        TranslationRule(
            pattern=Circuit.from_tuples(quasar_d, [("RBS", {}, [0, 1])]),
            replacement=Circuit.from_tuples(
                braket_d,
                [
                    ("H", {}, [0]),
                    ("H", {}, [1]),
                    ("CZ", {}, [0, 1]),
                    # Note!  We don't double_angle there because the angle
                    # to give to ry is actually theta/2
                    ("Ry", {"angle": lambda pm: pm[(0, "theta")]}, [0]),
                    ("Ry", {"angle": lambda pm: -pm[(0, "theta")]}, [1]),
                    ("CZ", {}, [0, 1]),
                    ("H", {}, [0]),
                    ("H", {}, [1]),
                ],
            ),
        ),
        TranslationRule(
            pattern=Circuit.from_tuples(quasar_d, [("RBS", {}, [0, 1])]),
            replacement=Circuit.from_tuples(
                braket_d,
                [
                    ("H", {}, [0]),
                    ("H", {}, [1]),
                    # sub for CZ
                    ("H", {}, [1]),
                    ("CNot", {}, [0, 1]),
                    ("H", {}, [1]),
                    # Note!  We don't double_angle there because the angle
                    # to give to ry is actually theta/2
                    ("Ry", {"angle": lambda pm: pm[(0, "theta")]}, [0]),
                    ("Ry", {"angle": lambda pm: -pm[(0, "theta")]}, [1]),
                    # sub for CZ
                    ("H", {}, [1]),
                    ("CNot", {}, [0, 1]),
                    ("H", {}, [1]),
                    ("H", {}, [0]),
                    ("H", {}, [1]),
                ],
            ),
        ),
    ]
    # we create a list of "best rules" and remove those that evaluate to None.
    # there may be a more elegant way of doing this.
    other_rules = {
        x
        for x in {best_rule_for_instruction_set(rbs_rules, allowed_instructions)}
        if x is not None
    }

    rules: PSet[TranslationRule] = (
        cast(PSet[TranslationRule], pset())
        .union(trivial_rules(quasar_d, braket_d, trivial_gates))
        .union(other_rules)
    )
    filtered_rules = pset(
        (
            rule
            for rule in rules
            if rule_matches_instruction_set(rule, allowed_instructions)
        )
    )
    return TranslationSet.from_trivial_rules(
        from_dialect=quasar_d, to_dialect=braket_d, rules=filtered_rules
    )


target_gatenames = sorted([x.name for x in translation_set().to_dialect.gate_defs])
untranslated = sorted([x.name for x in untranslated_gates(translation_set())])


def audit(c: quasar.Circuit, allowed_instructions: Optional[PSet[str]]) -> Dict:
    ir_audit = quasar_dialect.audit(c)
    if len(ir_audit.keys()) > 0:
        return ir_audit

    irc = quasar_dialect.native_to_ir(c)
    untranslatable = untranslatable_instructions(
        irc, translation_set(allowed_instructions)
    )

    result = {}
    if len(untranslatable) > 0:
        result["untranslatable_instructions"] = untranslatable
    if not quasar.Circuit.test_equivalence(c, c.center()):
        result["circuit_not_centered"] = True  # type: ignore
    return result


def native_is_translatable(
    c: quasar.Circuit, allowed_instructions: Optional[PSet[str]] = None
):
    """
    A native quasar circuit is translatable to braket if it
    is "centered" (ie no leading qubits)
    """
    return len(audit(c, allowed_instructions)) == 0


def translate(
    c: quasar.Circuit, allowed_instructions: Optional[PSet[str]] = None
) -> braket.circuits.Circuit:
    """
    Native-to-native translation
    """
    if not native_is_translatable(c, allowed_instructions):
        raise TranslationException(audit(c, allowed_instructions))
    try:
        return thread_first(
            c,
            quasar_dialect.native_to_ir,
            lambda x: simple_translate(translation_set(allowed_instructions), x),
            braket_dialect.ir_to_native,
            braket_dialect.occupy_empty_qubits,
        )
    except ViolationError:
        raise TranslationException(audit(c, allowed_instructions))
