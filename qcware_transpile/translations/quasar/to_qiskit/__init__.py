from qcware_transpile.matching import (TranslationRule, TranslationSet,
                                       trivial_rule, trivial_rules,
                                       untranslated_gates, simple_translate,
                                       circuit_is_simply_translatable_by)
from qcware_transpile.dialects import (quasar as quasar_dialect, qiskit as
                                       qiskit_dialect)
from qcware_transpile.circuits import Circuit
from qcware_transpile.instructions import Instruction
from dpcontracts import require
import quasar
from pyrsistent import pset
import qiskit
from toolz.functoolz import thread_first


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
            pattern=Circuit.from_tuples(quasar_d, [('RBS', {}, [0, 1])]),
            replacement=Circuit.from_tuples(
                qiskit_d, [('CXGate', {}, [1, 0]),
                           ('CRYGate', {
                               'theta': lambda pm: double_angle(pm[
                                   (0, 'theta')])
                           }, [0, 1]), ('CXGate', {}, [1, 0])]))
    }
    # the U2/U3 rules are disabled for now as they seem to be problematic
    # in qiskit when comparing resultant statevectors
    u2u3_rules = {  # noqa F841
        TranslationRule(pattern=Circuit.from_tuples(quasar_d,
                                                    [('u2', {}, [0])]),
                        replacement=Circuit.from_tuples(
                            qiskit_d, [('U2Gate', {
                                'phi': lambda pm: pm[(0, 'phi')],
                                'lam': lambda pm: pm[(0, 'lam')]
                            }, [0])])),
        TranslationRule(pattern=Circuit.from_tuples(quasar_d,
                                                    [('u3', {}, [0])]),
                        replacement=Circuit.from_tuples(
                            qiskit_d, [('U3Gate', {
                                'theta': lambda pm: pm[(0, 'theta')],
                                'phi': lambda pm: pm[(0, 'phi')],
                                'lam': lambda pm: pm[(0, 'lam')]
                            }, [0])]))
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


@require("Native circuit must be translatable",
         lambda args: native_is_translatable(args.c))
def to_qiskit(c: quasar.Circuit) -> qiskit.QuantumCircuit:
    """
    Native-to-native translation
    """
    return thread_first(c, quasar_dialect.native_to_circuit,
                        lambda x: simple_translate(translation_set(), x),
                        qiskit_dialect.circuit_to_native)
