from hypothesis import given, note, assume, settings
from qcware_transpile.translations.qiskit.to_quasar import translation_set, native_is_translatable  # type: ignore
from qcware_transpile.matching import translated_gates, simple_translate
from qcware_transpile.dialects import qiskit as qiskit_dialect, quasar as quasar_dialect
from ...strategies.qiskit import gates, circuits
import qiskit  # type: ignore
import quasar  # type: ignore
import numpy  # type: ignore


ts = translation_set()
translatable_gatedefs = [x for x in translated_gates(translation_set())]
translatable_circuits=circuits(1,3,1,4, gates(gate_list=translatable_gatedefs))

def quasar_statevector(circuit: quasar.Circuit):
    b = quasar.QuasarSimulatorBackend()
    sv = b.run_statevector(circuit)
    return sv

def qiskit_statevector(circuit: qiskit.QuantumCircuit):
    backend = qiskit.Aer.get_backend('statevector_simulator')
    sv = qiskit.execute(circuit, backend).result().data()['statevector']
    return sv

@given(translatable_circuits)
@settings(deadline=None)
def test_translate_qiskit_to_quasar(qiskit_circuit):
    assume(native_is_translatable(qiskit_circuit))
    note(qiskit_circuit.draw())
    qiskit_transpilation_circuit = qiskit_dialect.native_to_ir(qiskit_circuit)
    note(str(qiskit_transpilation_circuit))
    quasar_transpiled_circuit = simple_translate(ts, qiskit_transpilation_circuit)
    note(str(quasar_transpiled_circuit))
    quasar_native_circuit = quasar_dialect.ir_to_native(quasar_transpiled_circuit)
    note(str(quasar_native_circuit))
    sv_quasar = quasar_statevector(quasar_native_circuit)
    sv_qiskit = qiskit_statevector(qiskit_circuit)
    # this can fail with the default atol
    assert(numpy.allclose(sv_qiskit, sv_quasar))
