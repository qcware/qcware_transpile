import math
from hypothesis.strategies import (lists, integers, composite, sampled_from,
                                   floats, tuples)
import qiskit  # type: ignore
from qcware_transpile.dialects.qiskit.qiskit_dialect import (dialect,
                                                             gate_names)


@composite
def gates(draw, gate_list=sorted(dialect().gate_defs)):
    gate_def = draw(sampled_from(gate_list))
    gate_class = getattr(qiskit.circuit.library, gate_def.name)
    kwargs = {}
    angles = floats(min_value=0, max_value=2 * math.pi)
    for p in gate_def.parameter_names:
        value = draw(angles)
        kwargs[p] = value
    try:
        result = gate_class(**kwargs)
    except Exception as e:
        print(f"Exception creating gate {gate_def.name} with parms {kwargs}")
        raise e
    return result


@composite
def circuits(draw, min_qubits, max_qubits, min_length, max_length):
    length = draw(integers(min_value=min_length, max_value=max_length))
    num_qubits = draw(integers(min_value=min_qubits, max_value=max_qubits))
    qr = qiskit.QuantumRegister(num_qubits)

    circuit_gates = draw(
        lists(gates(), min_size=length, max_size=length).filter(
            lambda x: all([y.num_qubits <= num_qubits for y in x])))

    result = qiskit.QuantumCircuit(qr)
    for gate in circuit_gates:
        qubits = draw(
            lists(integers(min_value=0, max_value=num_qubits - 1),
                  min_size=gate.num_qubits,
                  max_size=gate.num_qubits,
                  unique=True))
        result.append(gate, tuple(qubits))
    return result


# circuits(1,3,1,5).example()
