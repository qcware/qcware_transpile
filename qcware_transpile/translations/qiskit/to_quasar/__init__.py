from qcware_transpile.matching import (TranslationRule, TranslationSet,
                                       trivial_rule, trivial_rules,
                                       untranslated_gates, simple_translate,
                                       circuit_is_simply_translatable_by,
                                       untranslatable_instructions)
from qcware_transpile.dialects import quasar as quasar_dialect, qiskit as qiskit_dialect
import qiskit
from qcware_transpile.circuits import Circuit
from qcware_transpile import TranslationException
from qcware_transpile.instructions import Instruction
from pyrsistent import pset
from dpcontracts import require, PreconditionError
import quasar
from toolz.functoolz import thread_first


def half_angle(theta):
    return theta / 2.0


def translation_set():
    """
    Creates a translation set from quasar to qiskit
    """
    trivial_gates = {('IGate', 'I'), ('HGate', 'H'), ('XGate', 'X'),
                     ('YGate', 'Y'), ('ZGate', 'Z'), ('SGate', 'S'),
                     ('TGate', 'T'), ('CXGate', 'CX'), ('CYGate', 'CY'),
                     ('CZGate', 'CZ'), ('CCXGate', 'CCX'),
                     ('SwapGate', 'SWAP'), ('U1Gate', 'u1'),
                     ('CSwapGate', 'CSWAP'), ('RXGate', 'Rx', half_angle),
                     ('RYGate', 'Ry', half_angle),
                     ('RZGate', 'Rz', half_angle)}

    quasar_d = quasar_dialect.dialect()
    qiskit_d = qiskit_dialect.dialect()
    # the u2/u3 rules are included but disabled due to flakiness
    # between quasar and qiskit.  Qiskit appears to be in the wrong
    # for this.
    u2u3_rules = {  # noqa F841
        TranslationRule(pattern=Circuit.from_instructions(
            dialect_name=qiskit_d.name,
            instructions=[
                Instruction(gate_def=qiskit_d.gate_named('U2Gate'),
                            parameter_bindings={},
                            bit_bindings=[0])
            ]),
                        replacement=Circuit.from_instructions(
                            dialect_name=quasar_d.name,
                            instructions=[
                                Instruction(gate_def=quasar_d.gate_named('u2'),
                                            parameter_bindings={
                                                'phi': lambda pm: pm[
                                                    (0, 'phi')],
                                                'lam': lambda pm: pm[
                                                    (0, 'lam')]
                                            },
                                            bit_bindings=[0])
                            ])),
        TranslationRule(pattern=Circuit.from_instructions(
            dialect_name=qiskit_d.name,
            instructions=[
                Instruction(gate_def=qiskit_d.gate_named('U3Gate'),
                            parameter_bindings={},
                            bit_bindings=[0])
            ]),
                        replacement=Circuit.from_instructions(
                            dialect_name=quasar_d.name,
                            instructions=[
                                Instruction(gate_def=quasar_d.gate_named('u3'),
                                            parameter_bindings={
                                                'theta':
                                                lambda pm: pm[(0, 'theta')],
                                                'phi':
                                                lambda pm: pm[(0, 'phi')],
                                                'lam':
                                                lambda pm: pm[(0, 'lam')]
                                            },
                                            bit_bindings=[0])
                            ]))
    }
    rules = pset().union(trivial_rules(qiskit_d, quasar_d, trivial_gates))
    return TranslationSet(from_dialect=qiskit_d,
                          to_dialect=quasar_d,
                          rules=rules)


target_gatenames = sorted(
    [x.name for x in translation_set().to_dialect.gate_defs])
untranslated = sorted([x.name for x in untranslated_gates(translation_set())])


def audit(c: qiskit.QuantumCircuit):
    """
    Tries to return a list of issues with the circuit which would
    make it untranslatable
    """
    ir_audit = qiskit_dialect.audit(c)
    if len(ir_audit) > 0:
        return ir_audit

    qdc = qiskit_dialect.native_to_ir(c)
    untranslatable = untranslatable_instructions(qdc, translation_set())

    circuit_qubits = sorted(list(qdc.qubits))
    used_qubits = sorted(
        list(set().union(*[set(i.bit_bindings) for i in qdc.instructions])))

    unused_edge_qubits = {
        x
        for x in circuit_qubits
        if (x < used_qubits[0]) or (x > used_qubits[-1])
    }

    result = {}
    if len(untranslatable) > 0:
        result['untranslatable_instructions'] = untranslatable
    if len(unused_edge_qubits) > 0:
        result['unused_edge_qubits'] = unused_edge_qubits
    return result


def native_is_translatable(c: qiskit.QuantumCircuit):
    """
    A native circuit is translatable to quasar if it has no leading or
    following "empty" qubits as currently there is no way to express this in quasar
    """
    return len(audit(c)) == 0


def translate(c: qiskit.QuantumCircuit) -> quasar.Circuit:
    """
    Native-to-native translation
    """
    try:
        return thread_first(c, qiskit_dialect.native_to_ir,
                            lambda x: simple_translate(translation_set(), x),
                            quasar_dialect.ir_to_native)
    except PreconditionError:
        raise TranslationException(audit(c))
