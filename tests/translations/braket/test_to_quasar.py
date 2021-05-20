from hypothesis import given, note, assume, settings
from qcware_transpile.translations.braket.to_quasar import (
    translation_set,
    native_is_translatable,
    translate,
)
from qcware_transpile.matching import translated_gates, simple_translate
from qcware_transpile.dialects import braket as braket_dialect, quasar as quasar_dialect
from ...strategies.braket import gates, circuits
import braket.circuits
import braket.devices
import quasar
import numpy

ts = translation_set()
translatable_gatedefs = [x for x in translated_gates(translation_set())]
translatable_circuits = circuits(1, 3, 1, 4, gates(gate_list=translatable_gatedefs))


def quasar_statevector(circuit: quasar.Circuit):
    b = quasar.QuasarSimulatorBackend()
    sv = b.run_statevector(circuit)
    return sv


def braket_statevector(circuit: braket.circuits.Circuit):
    b = braket.devices.LocalSimulator()
    sv = b.run(circuit.state_vector(), shots=0).result().values[0]
    return sv


@given(translatable_circuits)
@settings(deadline=None)
def test_translate_braket_to_quasar(braket_circuit):
    note(str(braket_circuit))
    assume(native_is_translatable(braket_circuit))
    modified_braket_circuit = braket_dialect.occupy_empty_qubits(braket_circuit)
    note(str(modified_braket_circuit))
    quasar_native_circuit = translate(braket_circuit)
    note(str(quasar_native_circuit))
    sv_quasar = quasar_statevector(quasar_native_circuit)
    sv_braket = braket_statevector(modified_braket_circuit)
    assert numpy.allclose(sv_braket, sv_quasar)
