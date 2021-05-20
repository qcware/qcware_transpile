from ..strategies.braket import circuits
from braket.circuits import Circuit
from qcware_transpile.dialects.braket import (
    native_to_ir,
    ir_to_native,
    native_circuits_are_equivalent,
)
from hypothesis import given, note, settings


@given(circuits(min_qubits=1, max_qubits=4, min_length=1, max_length=3))
@settings(deadline=None)
def test_conversion(qc):
    c = native_to_ir(qc)
    qc2 = ir_to_native(c)
    assert native_circuits_are_equivalent(qc, qc2)
