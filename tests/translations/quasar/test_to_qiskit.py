from hypothesis import given, note, assume, settings
from qcware_transpile.translations.quasar.to_qiskit import translation_set, native_is_translatable  # type: ignore
from qcware_transpile.matching import translated_gates, simple_translate
from qcware_transpile.dialects import qiskit as qiskit_dialect, quasar as quasar_dialect
from ...strategies.quasar import gates, circuits
import qiskit  # type: ignore
from qiskit.providers.aer import AerSimulator
import quasar  # type: ignore
import numpy  # type: ignore

ts = translation_set()
translatable_gatenames = [x.name for x in translated_gates(translation_set())]
translatable_circuits = circuits(1, 3, 1, 4, gates(gate_list=translatable_gatenames))


def quasar_statevector(circuit: quasar.Circuit):
    b = quasar.QuasarSimulatorBackend()
    sv = b.run_statevector(circuit)
    return sv


def qiskit_statevector(circuit: qiskit.QuantumCircuit):
    backend = AerSimulator(method="statevector")
    c = circuit.copy()
    c.save_state("final_statevector")
    result_data = qiskit.execute(c, backend).result().data()
    sv = result_data["final_statevector"]
    return sv


@given(translatable_circuits)
@settings(deadline=None)
def test_translate_quasar_to_qiskit(quasar_circuit):
    assume(native_is_translatable(quasar_circuit))
    note(str(quasar_circuit))
    quasar_transpilation_circuit = quasar_dialect.native_to_ir(quasar_circuit)
    note(str(quasar_transpilation_circuit))
    qiskit_transpiled_circuit = simple_translate(ts, quasar_transpilation_circuit)
    note(str(qiskit_transpiled_circuit))
    qiskit_native_circuit = qiskit_dialect.ir_to_native(qiskit_transpiled_circuit)
    note(qiskit_native_circuit.draw())
    sv_quasar = quasar_statevector(quasar_circuit)
    sv_qiskit = qiskit_statevector(qiskit_native_circuit)
    assert numpy.allclose(sv_quasar, sv_qiskit)
