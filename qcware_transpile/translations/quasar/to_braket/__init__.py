from qcware_transpile.matching import (
    TranslationRule,
    TranslationSet,
    trivial_rules,
    untranslatable_instructions,
    untranslated_gates,
    simple_translate,
)
from qcware_transpile.dialects import quasar as quasar_dialect, braket as braket_dialect
from qcware_transpile.circuits import Circuit
from qcware_transpile import TranslationException
from pyrsistent import pset
from icontract.errors import ViolationError
import braket.circuits
import quasar
from toolz.functoolz import thread_first
from typing import Dict


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


def translation_set():
    """
    Creates a translation set from quasar to braket
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
    other_rules = {
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
        )
    }

    rules = (
        pset()
        .union(trivial_rules(quasar_d, braket_d, trivial_gates))
        .union(other_rules)
    )
    return TranslationSet(from_dialect=quasar_d, to_dialect=braket_d, rules=rules)


target_gatenames = sorted([x.name for x in translation_set().to_dialect.gate_defs])
untranslated = sorted([x.name for x in untranslated_gates(translation_set())])


def audit(c: quasar.Circuit) -> Dict:
    ir_audit = quasar_dialect.audit(c)
    if len(ir_audit.keys()) > 0:
        return ir_audit

    irc = quasar_dialect.native_to_ir(c)
    untranslatable = untranslatable_instructions(irc, translation_set())

    result = {}
    if len(untranslatable) > 0:
        result["untranslatable_instructions"] = untranslatable
    if not quasar.Circuit.test_equivalence(c, c.center()):
        result["circuit_not_centered"] = True  # type: ignore
    return result


def native_is_translatable(c: quasar.Circuit):
    """
    A native quasar circuit is translatable to braket if it
    is "centered" (ie no leading qubits)
    """
    return len(audit(c)) == 0


def translate(c: quasar.Circuit) -> braket.circuits.Circuit:
    """
    Native-to-native translation
    """
    if not native_is_translatable(c):
        raise TranslationException(audit(c))
    try:
        return thread_first(
            c,
            quasar_dialect.native_to_ir,
            lambda x: simple_translate(translation_set(), x),
            braket_dialect.ir_to_native,
            braket_dialect.occupy_empty_qubits,
        )
    except ViolationError:
        raise TranslationException(audit(c))
