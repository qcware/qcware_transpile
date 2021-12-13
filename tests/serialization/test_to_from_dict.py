from hypothesis import given
from quasar import Circuit  # type: ignore

from qcware_transpile.dialects.quasar import ir_to_native, native_to_ir, dialect
from qcware_transpile.serialization import circuit_to_dict, dict_to_circuit
from tests.strategies.quasar import circuits


@given(circuits(min_qubits=1, max_qubits=4, min_length=1, max_length=3))
def test_conversion(qc):
    c = native_to_ir(qc)
    dc = circuit_to_dict(c)
    c2 = dict_to_circuit(dc, dialect())
    qc2 = ir_to_native(c2)
    assert Circuit.test_equivalence(qc, qc2)
