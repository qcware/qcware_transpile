from ..strategies.quasar import circuits
from quasar import Circuit
from qcware_transpile.dialects.quasar import native_to_circuit, circuit_to_native
from hypothesis import given


@given(circuits(min_qubits=1, max_qubits=4, min_length=1, max_length=3))
def test_conversion(qc):
    c = native_to_circuit(qc)
    qc2 = circuit_to_native(c)
    assert Circuit.test_equivalence(qc, qc2)
