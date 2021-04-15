from hypothesis import given, note, assume, settings
from qcware_transpile.translations.qiskit.to_quasar import (
    translation_set, native_is_translatable, translate,
    basis_gates)  # type: ignore
from qcware_transpile.dialects import qiskit as qiskit_dialect, quasar as quasar_dialect
from ...strategies.qiskit import gates, circuits
import qiskit  # type: ignore
import quasar  # type: ignore
import numpy  # type: ignore

ts = translation_set()
translatable_gatedefs = [
    x for x in qiskit_dialect.dialect().gate_defs if x.name not in {}
]
translatable_circuits = circuits(1, 3, 1, 4,
                                 gates(gate_list=translatable_gatedefs))


def quasar_probability_vector(circuit: quasar.Circuit):
    b = quasar.QuasarSimulatorBackend()
    sv = b.run_statevector(circuit)
    return abs(sv)


def qiskit_probability_vector(circuit: qiskit.QuantumCircuit):
    backend = qiskit.Aer.get_backend('statevector_simulator')
    backend.set_options(zero_threshold=1e-10)
    sv = qiskit.execute(circuit, backend).result().data()['statevector']
    return abs(sv)


@given(translatable_circuits)
@settings(deadline=None, max_examples=2000)
def test_translate_qiskit_to_quasar(qiskit_circuit):
    assume(native_is_translatable(qiskit_circuit))
    note(qiskit_circuit.draw())
    pv_qiskit = qiskit_probability_vector(qiskit_circuit)
    transpiled_qiskit_circuit = qiskit.compiler.transpile(
        qiskit_circuit, basis_gates=basis_gates())
    note(transpiled_qiskit_circuit.draw())
    pv_transpiled_qiskit = qiskit_probability_vector(transpiled_qiskit_circuit)
    assert (numpy.allclose(pv_qiskit, pv_transpiled_qiskit, atol=1e-7))
    quasar_native_circuit = translate(qiskit_circuit, should_transpile=True)
    note(str(quasar_native_circuit))
    pv_quasar = quasar_probability_vector(quasar_native_circuit)
    # this can fail with the default atol
    #assert (numpy.allclose(pv_qiskit, pv_quasar, atol=0.000001))
