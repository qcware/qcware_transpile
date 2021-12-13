import math
from hypothesis.strategies import lists, integers, composite, sampled_from, floats
from braket.circuits import Circuit, Gate, Instruction
from qcware_transpile.dialects.braket.braket_dialect import dialect


@composite
def gates(draw, gate_list=sorted(dialect().gate_defs)):
    gate_def = draw(sampled_from(gate_list))
    kwargs = {}
    angles = floats(min_value=0, max_value=2 * math.pi)
    for p in gate_def.parameter_names:
        value = draw(angles)
        kwargs[p] = value
    try:
        result = getattr(Gate, gate_def.name)(**kwargs)
    except Exception as e:
        print(f"Exception creating gate {gate_def.name} with params {kwargs}")
        raise e
    return result


@composite
def circuits(draw, min_qubits, max_qubits, min_length, max_length, gates=gates()):
    length = draw(integers(min_value=min_length, max_value=max_length))
    num_qubits = draw(integers(min_value=min_qubits, max_value=max_qubits))
    circuit_gates = draw(
        lists(gates, min_size=length, max_size=length).filter(
            lambda x: all([y.qubit_count <= num_qubits for y in x])
        )
    )
    result = Circuit()
    for gate in circuit_gates:
        qubits = draw(
            lists(
                integers(min_value=0, max_value=num_qubits - 1),
                min_size=gate.qubit_count,
                max_size=gate.qubit_count,
                unique=True,
            )
        )
        instruction = Instruction(gate, qubits)
        result.add_instruction(instruction)
    return result
