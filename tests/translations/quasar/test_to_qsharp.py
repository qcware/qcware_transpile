from hypothesis import given, note, assume, settings
from qcware_transpile.translations.quasar.to_qsharp import translation_set, native_is_translatable 
from qcware_transpile.matching import translated_gates, simple_translate
from qcware_transpile.dialects import qsharp as qsharp_dialect, quasar as quasar_dialect
from qcware_transpile.circuits import reverse_circuit
from ...strategies.quasar import gates, circuits
from ...strategies.qsharp import run_generated_circuit
from qsharp import compile
import quasar
import numpy

ts = translation_set()
translatable_gatenames = [x.name for x in translated_gates(translation_set())]
translatable_circuits = circuits(1, 3, 1, 4,
                                 gates(gate_list=translatable_gatenames))


def quasar_statevector(circuit: quasar.Circuit):
    b = quasar.QuasarSimulatorBackend()
    sv = b.run_statevector(circuit)
    return sv


def qsharp_statevector(circuit: str):
    return run_generated_circuit(circuit)


@given(translatable_circuits)
@settings(deadline=None)
def test_translate_quasar_to_qsharp(quasar_circuit):
    assume(native_is_translatable(quasar_circuit))
    note(str(quasar_circuit))
    quasar_transpilation_circuit = quasar_dialect.native_to_ir(quasar_circuit)
    note(str(quasar_transpilation_circuit))
    reversed_quasar_transpilation_circuit = reverse_circuit(quasar_transpilation_circuit)
    note(str(reversed_quasar_transpilation_circuit))
    qsharp_transpiled_circuit = simple_translate(ts,
                                                 reversed_quasar_transpilation_circuit)
    note(str(qsharp_transpiled_circuit))
    qsharp_native_circuit = qsharp_dialect.ir_to_native(
        qsharp_transpiled_circuit)
    note(str(qsharp_native_circuit))
    sv_quasar = quasar_statevector(quasar_circuit)
    sv_qsharp = qsharp_statevector(qsharp_native_circuit)
    assert (numpy.allclose(sv_quasar, sv_qsharp, atol=1e-07))