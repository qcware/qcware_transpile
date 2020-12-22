from qcware_transpile.matching import (TranslationRule, TranslationSet,
                                       trivial_rule, trivial_rules,
                                       untranslated_gates,
                                       circuit_is_simply_translatable_by)
from qcware_transpile.dialects import quasar as quasar_dialect, qiskit as qiskit_dialect
from qcware_transpile.circuits import Circuit
from qcware_transpile.instructions import Instruction
import quasar
from pyrsistent import pset


def double_angle(theta):
    return 2 * theta


def translation_set():
    """
    Creates a translation set from quasar to qiskit
    """
    trivial_gates = {('I', 'IGate'), ('H', 'HGate'), ('X', 'XGate'),
                     ('Y', 'YGate'), ('Z', 'ZGate'), ('S', 'SGate'),
                     ('T', 'TGate'), ('CX', 'CXGate'), ('CY', 'CYGate'),
                     ('CZ', 'CZGate'), ('CCX', 'CCXGate'), ('u1', 'U1Gate'),
                     ('SWAP', 'SwapGate'), ('CSWAP', 'CSwapGate'),
                     ('Rx', 'RXGate', double_angle),
                     ('Ry', 'RYGate', double_angle),
                     ('Rz', 'RZGate', double_angle)}

    quasar_d = quasar_dialect.dialect()
    qiskit_d = qiskit_dialect.dialect()
    other_rules = {
        TranslationRule(
            pattern=Circuit.from_instructions(
                quasar_d.name,
                instructions=[
                    Instruction(gate_def=quasar_d.gate_named('RBS'),
                                parameter_bindings={},
                                bit_bindings=[0, 1])
                ]),
            replacement=Circuit.from_instructions(
                qiskit_d.name,
                instructions=[
                    Instruction(gate_def=qiskit_d.gate_named('CXGate'),
                                parameter_bindings={},
                                bit_bindings=[1, 0]),
                    Instruction(gate_def=qiskit_d.gate_named('CRYGate'),
                                parameter_bindings={
                                    'theta':
                                    lambda pm: double_angle(pm[(0, 'theta')])
                                },
                                bit_bindings=[0, 1]),
                    Instruction(gate_def=qiskit_d.gate_named('CXGate'),
                                parameter_bindings={},
                                bit_bindings=[1, 0])
                ])),
        TranslationRule(pattern=Circuit.from_instructions(
            dialect_name=quasar_d.name,
            instructions=[
                Instruction(gate_def=quasar_d.gate_named('u2'),
                            parameter_bindings={},
                            bit_bindings=[0])
            ]),
                        replacement=Circuit.from_instructions(
                            dialect_name=qiskit_d.name,
                            instructions=[
                                Instruction(
                                    gate_def=qiskit_d.gate_named('U2Gate'),
                                    parameter_bindings={
                                        'phi': lambda pm: pm[(0, 'phi')],
                                        'lam': lambda pm: pm[(0, 'lam')]
                                    },
                                    bit_bindings=[0])
                            ])),
        TranslationRule(pattern=Circuit.from_instructions(
            dialect_name=quasar_d.name,
            instructions=[
                Instruction(gate_def=quasar_d.gate_named('u3'),
                            parameter_bindings={},
                            bit_bindings=[0])
            ]),
                        replacement=Circuit.from_instructions(
                            dialect_name=qiskit_d.name,
                            instructions=[
                                Instruction(
                                    gate_def=qiskit_d.gate_named('U3Gate'),
                                    parameter_bindings={
                                        'theta': lambda pm: pm[(0, 'theta')],
                                        'phi': lambda pm: pm[(0, 'phi')],
                                        'lam': lambda pm: pm[(0, 'lam')]
                                    },
                                    bit_bindings=[0])
                            ]))
    }

    rules = pset().union(trivial_rules(quasar_d, qiskit_d,
                                       trivial_gates)).union(other_rules)
    return TranslationSet(from_dialect=quasar_d,
                          to_dialect=qiskit_d,
                          rules=rules)


target_gatenames = sorted(
    [x.name for x in translation_set().to_dialect.gate_defs])
untranslated = sorted([x.name for x in untranslated_gates(translation_set())])


def native_is_translatable(c: quasar.Circuit):
    """
    A native quasar circuit is translatable to qiskit if it
    is "centered" (ie no leading qubits)
    """
    return quasar.Circuit.test_equivalence(
        c, c.center()) and circuit_is_simply_translatable_by(
            quasar_dialect.native_to_circuit(c), translation_set())
