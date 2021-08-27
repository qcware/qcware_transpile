import braket.circuits
import braket.devices
import numpy
import pytest
import quasar
from hypothesis import assume, given, note, reproduce_failure, settings
from hypothesis.strategies import composite, sampled_from

from qcware_transpile.dialects import braket as braket_dialect
from qcware_transpile.dialects import quasar as quasar_dialect
from qcware_transpile.matching import simple_translate, translated_gates
from qcware_transpile.translations.quasar.to_braket import (
    native_is_translatable,
    translation_set,
)

from ...strategies.quasar import circuits, gates

ionq_operations = [
    "x",
    "y",
    "z",
    "rx",
    "ry",
    "rz",
    "h",
    "cnot",
    "s",
    "si",
    "t",
    "ti",
    "v",
    "vi",
    "xx",
    "yy",
    "zz",
    "swap",
    "i",
]
rigetti_operations = [
    "cz",
    "xy",
    "ccnot",
    "cnot",
    "cphaseshift",
    "cphaseshift00",
    "cphaseshift01",
    "cphaseshift10",
    "cswap",
    "h",
    "i",
    "iswap",
    "phaseshift",
    "pswap",
    "rx",
    "ry",
    "rz",
    "s",
    "si",
    "swap",
    "t",
    "ti",
    "x",
    "y",
    "z",
]
all_operations = None


@composite
def translation_set_and_circuits(draw, allowed_target_instruction_sets):
    ts = translation_set(draw(sampled_from(allowed_target_instruction_sets)))
    translatable_gatenames = [x.name for x in translated_gates(ts)]
    circuit_result = draw(circuits(1, 3, 1, 4, gates(gate_list=translatable_gatenames)))
    return ts, circuit_result


def quasar_statevector(circuit: quasar.Circuit):
    b = quasar.QuasarSimulatorBackend()
    sv = b.run_statevector(circuit)
    return sv


def braket_statevector(circuit: braket.circuits.Circuit):
    b = braket.devices.LocalSimulator()
    sv = b.run(circuit.state_vector(), shots=0).result().values[0]
    return sv


def check_translate_quasar_to_braket(ts_and_circuit):
    ts, quasar_circuit = ts_and_circuit
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


@given(translation_set_and_circuits([rigetti_operations, ionq_operations, None]))
@settings(deadline=None)
# @reproduce_failure('6.9.1', b'AAEBEgABYyGxCRIBAxVAQo8e/AAAAQ==')
# @reproduce_failure('6.9.1', b'AAEBAQAAACFgpsgcAAAB')
# @reproduce_failure('6.9.1', b'AAEBEAcAAANWdxNeAAAB')
# @reproduce_failure('6.9.1', b'AAEBAAsAAAAA2r47AAAB')
def test_random_circuits(ts_and_circuit):
    check_translate_quasar_to_braket(ts_and_circuit)


@pytest.mark.parametrize(
    "allowed_instructions", [ionq_operations, rigetti_operations, all_operations]
)
@given(circuits(1, 3, 1, 4, gates(gate_list=["RBS"])))
def test_rbs_(allowed_instructions, circuit):
    ts = translation_set(allowed_instructions)
    check_translate_quasar_to_braket(tuple((ts, circuit)))
