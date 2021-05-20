from qcware_transpile.matching import (
    TranslationRule,
    TranslationSet,
    trivial_rules,
    untranslatable_instructions,
    simple_translate,
)
from qcware_transpile.dialects import quasar as quasar_dialect, qsharp as qsharp_dialect
from qcware_transpile.circuits import Circuit, reverse_circuit
from qcware_transpile import TranslationException
from pyrsistent import pset
from icontract.errors import ViolationError
import quasar
from toolz.functoolz import thread_first
from typing import Dict


def double_angle(theta):
    return 2 * theta


def translation_set():
    """
    Creates a translation set from quasar to qsharp
    """
    trivial_gates = {
        ("I", "I"),
        ("H", "H"),
        ("X", "X"),
        ("Y", "Y"),
        ("Z", "Z"),
        ("S", "S"),
        ("T", "T"),
        ("CX", "CNOT"),
        ("CCX", "CCNOT"),
        ("u1", "R1"),
        ("SWAP", "SWAP"),
        ("Rx", "Rx", double_angle),
        ("Ry", "Ry", double_angle),
        ("Rz", "Rz", double_angle),
        ("CY", "CY"),
        ("CZ", "CZ"),
    }

    quasar_d = quasar_dialect.dialect()
    qsharp_d = qsharp_dialect.dialect()
    other_rules = {
        TranslationRule(
            pattern=Circuit.from_tuples(quasar_d, [("RBS", {}, [0, 1])]),
            replacement=Circuit.from_tuples(
                qsharp_d,
                [
                    ("H", {}, [0]),
                    ("H", {}, [1]),
                    ("CZ", {}, [0, 1]),
                    # Note!  We don't double_angle there because the angle
                    # to give to ry is actually theta/2
                    ("Ry", {"theta": lambda pm: pm[(0, "theta")]}, [0]),
                    ("Ry", {"theta": lambda pm: -pm[(0, "theta")]}, [1]),
                    ("CZ", {}, [0, 1]),
                    ("H", {}, [0]),
                    ("H", {}, [1]),
                ],
            ),
        )
    }

    rules = (
        pset()
        .union(trivial_rules(quasar_d, qsharp_d, trivial_gates))
        .union(other_rules)
    )
    return TranslationSet(from_dialect=quasar_d, to_dialect=qsharp_d, rules=rules)


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
    A native quasar circuit is translatable to qsharp if it
    is "centered" (ie no leading qubits)
    """
    return len(audit(c)) == 0


def translate(c: quasar.Circuit) -> str:
    """
    Native-to-native translation.
    """
    if not native_is_translatable(c):
        raise TranslationException(audit(c))
    try:
        return thread_first(
            c,
            quasar_dialect.native_to_ir,
            # reverse the bit order in the ir quasar circuit
            # since quasar uses big-endian representation and
            # qsharp uses little-endian representation
            reverse_circuit,
            lambda x: simple_translate(translation_set(), x),
            qsharp_dialect.ir_to_native,
        )
    except ViolationError:
        raise TranslationException(audit(c))
