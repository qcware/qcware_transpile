from ..strategies.qiskit import circuits
from qcware_transpile.dialects.qiskit import (native_to_ir, ir_to_native,
                                              native_circuits_are_equivalent)
from hypothesis import given, note, settings
import qiskit


@given(circuits(min_qubits=1, max_qubits=4, min_length=1, max_length=3))
@settings(deadline=None)
def test_conversion(qc):
    note(qc.draw())
    c = native_to_ir(qc)
    note(c)
    qc2 = ir_to_native(c)
    note(qc2.draw())
    backend = qiskit.Aer.get_backend('statevector_simulator')
    sv1 = qiskit.execute(qc, backend).result().data()['statevector']
    sv2 = qiskit.execute(qc2, backend).result().data()['statevector']
    note(sv1)
    note(sv2)
    assert native_circuits_are_equivalent(qc, qc2)
