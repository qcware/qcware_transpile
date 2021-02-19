from ..strategies.qiskit import circuits
from qcware_transpile.dialects.qiskit import (native_to_ir, ir_to_native,
                                              native_circuits_are_equivalent,
                                              normalized_instructions)
from hypothesis import given, note, settings
import qiskit
import numpy as np


@given(circuits(min_qubits=1, max_qubits=4, min_length=1, max_length=3))
@settings(deadline=None)
def test_conversion(qc):
    note(qc.draw())
    note(qc.data)
    c = native_to_ir(qc)
    note(c)
    qc2 = ir_to_native(c)
    note(qc2.draw())
    note(qc2.data)
    instruction_pairs = zip(normalized_instructions(qc),
                            normalized_instructions(qc2))
    for x in instruction_pairs:
        assert x[0] == x[1]
    assert native_circuits_are_equivalent(qc, qc2)
