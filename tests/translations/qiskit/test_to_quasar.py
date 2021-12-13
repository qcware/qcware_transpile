from hypothesis import given, note, assume, settings
from qcware_transpile.translations.qiskit.to_quasar import (
    translation_set,
    native_is_translatable,
    translate,
    instructions_after_last_measurement,
    audit,
)
from qcware_transpile.matching import simple_translate
from qcware_transpile.dialects import qiskit as qiskit_dialect
from ...strategies.qiskit import gates, circuits
import qiskit  # type: ignore
from qiskit.providers.aer import AerSimulator
import quasar  # type: ignore
import numpy  # type: ignore
import pytest

ts = translation_set()
translatable_gatedefs = [
    x for x in qiskit_dialect.dialect().gate_defs if x.name not in {"measure", "reset"}
]
translatable_circuits = circuits(1, 3, 1, 4, gates(gate_list=translatable_gatedefs))


def quasar_probability_vector(circuit: quasar.Circuit):
    b = quasar.QuasarSimulatorBackend()
    sv = b.run_statevector(circuit)
    return abs(sv)


def qiskit_probability_vector(circuit: qiskit.QuantumCircuit):
    backend = AerSimulator(method="statevector")
    c = circuit.copy()
    c.save_state("final_statevector")
    result_data = qiskit.execute(c, backend).result().data()
    sv = result_data["final_statevector"]
    return abs(sv)


def test_instructions_after_measurement():
    c = qiskit.QuantumCircuit(1, 1)
    c.h(0)
    c.measure(0, 0)
    ir_c = qiskit_dialect.native_to_ir(c)
    assert len(instructions_after_last_measurement(ir_c)) == 0
    assert "instructions_after_last_measurement" not in audit(c)

    c = qiskit.QuantumCircuit(1, 1)
    c.measure(0, 0)
    c.h(0)
    ir_c = qiskit_dialect.native_to_ir(c)
    assert len(instructions_after_last_measurement(ir_c)) == 1
    assert audit(c)["instructions_after_last_measurement"] == ["h"]

    c = qiskit.QuantumCircuit(1, 1)
    c.h(0)
    c.measure(0, 0)
    c.h(0)
    ir_c = qiskit_dialect.native_to_ir(c)
    assert len(instructions_after_last_measurement(ir_c)) == 1
    assert audit(c)["instructions_after_last_measurement"] == ["h"]


@given(translatable_circuits)
@settings(deadline=None)
def test_translate_qiskit_to_quasar(qiskit_circuit):
    note(qiskit_circuit.draw())
    assume(native_is_translatable(qiskit_circuit))
    quasar_native_circuit = translate(qiskit_circuit, should_transpile=True)
    note(str(quasar_native_circuit))
    pv_quasar = quasar_probability_vector(quasar_native_circuit)
    pv_qiskit = qiskit_probability_vector(qiskit_circuit)
    # this can fail with the default atol
    assert numpy.allclose(pv_qiskit, pv_quasar, atol=0.000001)
