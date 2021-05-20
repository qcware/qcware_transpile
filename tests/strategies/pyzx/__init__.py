import pyzx
from hypothesis.strategies import (
    lists,
    sampled_from,
    booleans,
    composite,
    floats,
    integers,
)
from hypothesis import assume
from qcware_transpile.dialects.pyzx import pyzx_dialect
from typing import Set
import numpy as np


@composite
def gates(
    draw, possible_qubits: Set[int], gate_list=sorted(pyzx_dialect.dialect().gate_defs)
):
    gate_def = draw(sampled_from(gate_list))
    gate_class = getattr(pyzx.circuit.gates, gate_def.name)
    num_qubits = len(gate_def.qubit_ids)
    assume(num_qubits < len(possible_qubits))
    qubits = draw(
        lists(
            sampled_from(sorted(list(possible_qubits))),
            unique=True,
            min_size=num_qubits,
            max_size=num_qubits,
        )
    )

    try:
        parameters = pyzx_dialect.pyzx_qubit_bindings(qubits)
    except ValueError:
        raise ValueError(f"Invalid number of qubits {qubits} for gate {gate_def.name}")
    for p in gate_def.parameter_names:
        if p == "adjoint":
            parameters[p] = draw(booleans())
        if p in ["theta", "phi", "phase"]:
            parameters[p] = draw(floats(min_value=0, max_value=2 * np.pi))

    return gate_class(**parameters)


@composite
def circuits(
    draw,
    min_qubits,
    max_qubits,
    min_length,
    max_length,
):
    length = draw(integers(min_value=min_length, max_value=max_length))
    num_qubits = draw(integers(min_value=min_qubits, max_value=max_qubits))
    result = pyzx.circuit.Circuit(num_qubits)

    circuit_gates = draw(
        lists(
            gates(possible_qubits=range(num_qubits)), min_size=length, max_size=length
        )
    )
    for gate in circuit_gates:
        result.add_gate(gate)

    return result
