from hypothesis import given, note, assume, settings
from qcware_transpile.translations.quasar.to_pyzx import translation_set, native_is_translatable  # type: ignore
import qcware_transpile.translations.pyzx.to_quasar as to_quasar  # type: ignore
from qcware_transpile.matching import translated_gates, simple_translate
from qcware_transpile.dialects import pyzx as pyzx_dialect, quasar as quasar_dialect
from ...strategies.quasar import gates, circuits
import pyzx  # type: ignore
import quasar  # type: ignore
import numpy  # type: ignore
import pytest

ts = translation_set()
translatable_gatenames = [x.name for x in translated_gates(translation_set())]
translatable_circuits = circuits(1, 3, 1, 4, gates(gate_list=translatable_gatenames))


def quasar_statevector(circuit: quasar.Circuit):
    b = quasar.QuasarSimulatorBackend()
    sv = b.run_statevector(circuit)
    return sv


# skipping this for now.  The pyzx business appears to work, but
# generating random circuits with angles that translate roughly to
# fractions seems to generate tiny errors so if you're not doing angles
# by fractions, this may turn out to be too problematic to use.  Worth trying.
@pytest.mark.skip
@given(translatable_circuits)
@settings(deadline=None)
def test_translate_quasar_to_qiskit(quasar_circuit):
    assume(native_is_translatable(quasar_circuit))
    note(str(quasar_circuit))
    quasar_transpilation_circuit = quasar_dialect.native_to_ir(quasar_circuit)
    note(str(quasar_transpilation_circuit))
    pyzx_transpiled_circuit = simple_translate(ts, quasar_transpilation_circuit)
    note(str(pyzx_transpiled_circuit))
    pyzx_native_circuit = pyzx_dialect.ir_to_native(pyzx_transpiled_circuit)
    note(pyzx_native_circuit.gates)
    # we can't test statevector equivalence, so let's just translate back
    # and test the round trip
    g = pyzx_native_circuit.to_graph()
    pyzx.teleport_reduce(g)
    pyzx_optimized = pyzx.Circuit.from_graph(g)
    # pyzx.full_reduce(g)
    # pyzx_optimized = pyzx.extract_circuit(g.copy())
    note("Optimized pyzx")
    note(pyzx_optimized.gates)
    quasar_circuit_2 = to_quasar.translate(pyzx_optimized)
    note(str(quasar_circuit_2))
    # this peculiar business derives from the fact that Pyzx will happily
    # optimize some qubits out of existence.  We're just playing here.
    sv_quasar_1 = quasar_statevector(quasar_circuit)
    sv_quasar_2 = quasar_statevector(quasar_circuit_2)
    l = min(len(sv_quasar_1), len(sv_quasar_2))
    # big atol since the fractional business confuses some things
    assert numpy.allclose(sv_quasar_1[0:l], sv_quasar_2[0:l], atol=0.0001)
