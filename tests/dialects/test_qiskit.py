from ..strategies.qiskit import circuits
from qcware_transpile.dialects.qiskit import (
    native_to_ir,
    ir_to_native,
    native_circuits_are_equivalent,
)
from hypothesis import given, note, settings


@given(circuits(min_qubits=1, max_qubits=4, min_length=1, max_length=3))
@settings(deadline=None)
def test_conversion(qc):
    note(qc.draw())
    c = native_to_ir(qc)
    note(c)
    qc2 = ir_to_native(c)
    note(qc2.draw())
    assert native_circuits_are_equivalent(qc, qc2)
