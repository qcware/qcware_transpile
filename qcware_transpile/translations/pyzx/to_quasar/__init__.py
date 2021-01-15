from qcware_transpile.matching import (TranslationRule, TranslationSet,
                                       trivial_rule, trivial_rules,
                                       untranslated_gates, simple_translate,
                                       circuit_is_simply_translatable_by)
from qcware_transpile.dialects import quasar as quasar_dialect, pyzx as pyzx_dialect
import pyzx
from qcware_transpile.circuits import Circuit
from qcware_transpile.instructions import Instruction
from pyrsistent import pset
from dpcontracts import require
import quasar
from toolz.functoolz import thread_first
from fractions import Fraction
from numpy import pi


def from_phase_angle(phase: Fraction) -> float:
    """
    Pyzx seems to evaluate phase angles as a fraction of pi/2, so we must
    translate our quasar angles from that
    """
    return float(phase * pi)


def translation_set():
    """
    Creates a translation set from quasar to qiskit
    """
    trivial_gates = {
        ('HAD', 'H'),
        ('NOT', 'X'),
        ('CZ', 'CZ'),  # ('T', 'T', lambda pm: False),
        ('ZPhase', 'Rz', from_phase_angle),
        ('Z', 'Z'),
        ('CNOT', 'CX'),
        ('XPhase', 'Rx', from_phase_angle),
        ('SWAP', 'SWAP')
    }

    # the T and S gates can be adjoint in pyzx, although in quasar those
    # adjoints are the TT and ST gates respectively
    quasar_d = quasar_dialect.dialect()
    pyzx_d = pyzx_dialect.dialect()
    st_gates = {
        TranslationRule(
            pattern=Circuit.from_tuples(
                pyzx_d,
                [('T', {'adjoint': False}, [0])]),
            replacement=Circuit.from_tuples(
                quasar_d, [('T', {}, [0])])),
        TranslationRule(
            pattern=Circuit.from_tuples(
                pyzx_d,
                [('T', {'adjoint': True}, [0])]),
            replacement=Circuit.from_tuples(
                quasar_d, [('TT', {}, [0])])),
        TranslationRule(
            pattern=Circuit.from_tuples(
                pyzx_d,
                [('S', {'adjoint': False}, [0])]),
            replacement=Circuit.from_tuples(
                quasar_d, [('S', {}, [0])])),
        TranslationRule(
            pattern=Circuit.from_tuples(
                pyzx_d,
                [('S', {'adjoint': True}, [0])]),
            replacement=Circuit.from_tuples(
                quasar_d, [('ST', {}, [0])])),
    }
    rules = pset().union(trivial_rules(pyzx_d, quasar_d, trivial_gates)).union(st_gates)
    return TranslationSet(from_dialect=pyzx_d,
                          to_dialect=quasar_d,
                          rules=rules)


target_gatenames = sorted(
    [x.name for x in translation_set().to_dialect.gate_defs])
untranslated = sorted([x.name for x in untranslated_gates(translation_set())])


def native_is_translatable(c: pyzx.Circuit):
    """
    A native quasar circuit is translatable to qiskit if it
    is "centered" (ie no leading qubits) and is composed of translatable
    gates
    """
    return circuit_is_simply_translatable_by(
        pyzx_dialect.native_to_ir(c), translation_set())


@require("Native circuit must be translatable",
         lambda args: native_is_translatable(args.c))
def translate(c: pyzx.Circuit) -> quasar.Circuit:
    """
    Native-to-native translation
    """
    return thread_first(c, pyzx_dialect.native_to_ir,
                        lambda x: simple_translate(translation_set(), x),
                        quasar_dialect.ir_to_native)
