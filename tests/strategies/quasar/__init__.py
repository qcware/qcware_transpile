from hypothesis.strategies import (
    lists,
    integers,
    composite,
    sampled_from,
    floats,
    tuples,
)
from quasar.circuit import Gate, Circuit  # type: ignore
from qcware_transpile.dialects.quasar.quasar_dialect import quasar_gatenames_full
import inspect
import math


@composite
def gates(draw, gate_list=sorted(quasar_gatenames_full())):
    result = getattr(Gate, draw(sampled_from(gate_list)))
    if callable(result):
        s = inspect.signature(result)
        kwargs = {}
        angles = floats(min_value=0, max_value=2 * math.pi)
        for p in s.parameters:
            value = draw(angles)
            kwargs[p] = value
        result = result(**kwargs)
    return result


@composite
def circuits(draw, min_qubits, max_qubits, min_length, max_length, gates=gates()):
    length = draw(integers(min_value=min_length, max_value=max_length))
    num_qubits = draw(integers(min_value=min_qubits, max_value=max_qubits))
    circuit_gates = draw(
        lists(gates, min_size=length, max_size=length).filter(
            lambda x: all([y.nqubit <= num_qubits for y in x])
        )
    )
    result = Circuit()
    for gate in circuit_gates:
        qubits = draw(
            lists(
                integers(min_value=0, max_value=num_qubits - 1),
                min_size=gate.nqubit,
                max_size=gate.nqubit,
                unique=True,
            )
        )
        result.add_gate(gate, tuple(qubits))
    return result
