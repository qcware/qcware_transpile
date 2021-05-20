import braket.devices
from hypothesis import given, note, assume, settings, reproduce_failure
from qcware_transpile.translations.quasar.to_braket import (
    translation_set,
    native_is_translatable,
)
from qcware_transpile.matching import translated_gates, simple_translate
from qcware_transpile.dialects import braket as braket_dialect, quasar as quasar_dialect
from ...strategies.quasar import gates, circuits
import braket.circuits
import quasar
import numpy

ts = translation_set()
translatable_gatenames = [x.name for x in translated_gates(translation_set())]
translatable_circuits = circuits(1, 3, 1, 4, gates(gate_list=translatable_gatenames))


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
# @reproduce_failure('6.9.1', b'AAEBEgABYyGxCRIBAxVAQo8e/AAAAQ==')
# @reproduce_failure('6.9.1', b'AAEBAQAAACFgpsgcAAAB')
# @reproduce_failure('6.9.1', b'AAEBEAcAAANWdxNeAAAB')
# @reproduce_failure('6.9.1', b'AAEBAAsAAAAA2r47AAAB')
def test_translate_quasar_to_braket(quasar_circuit):
    assume(native_is_translatable(quasar_circuit))
    note(str(quasar_circuit))
    quasar_transpilation_circuit = quasar_dialect.native_to_ir(quasar_circuit)
    note(str(quasar_transpilation_circuit))
    braket_transpiled_circuit = simple_translate(ts, quasar_transpilation_circuit)
    note(str(braket_transpiled_circuit))
    braket_native_circuit = braket_dialect.ir_to_native(braket_transpiled_circuit)
    note(str(braket_native_circuit))
    modified_braket_native_circuit = braket_dialect.occupy_empty_qubits(
        braket_native_circuit
    )
    note(str(modified_braket_native_circuit))
    sv_quasar = quasar_statevector(quasar_circuit)
    sv_braket = braket_statevector(modified_braket_native_circuit)
    # this can fail with the default atol
    assert numpy.allclose(sv_quasar, sv_braket)
