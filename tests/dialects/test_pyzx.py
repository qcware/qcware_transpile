from ..strategies.pyzx import circuits
from pyzx import Circuit  # type: ignore
from qcware_transpile.dialects.pyzx import (
    native_to_ir,
    ir_to_native,
    native_circuits_are_equivalent,
)
from hypothesis import given, note, HealthCheck, settings


@given(circuits(min_qubits=1, max_qubits=4, min_length=1, max_length=3))
@settings(suppress_health_check=[HealthCheck.too_slow], deadline=None)
def test_conversion(qc):
    note(qc.gates)
    c = native_to_ir(qc)
    note(c)
    qc2 = ir_to_native(c)
    note(qc2.gates)
    assert native_circuits_are_equivalent(qc, qc2)
