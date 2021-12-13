import math
import numpy
from hypothesis import given, settings
from hypothesis.strategies import composite, floats, integers, lists, sampled_from
from itertools import product
from jinja2 import Template
from qcware_transpile.dialects.qsharp.qsharp_dialect import dialect, ir_to_native
from qcware_transpile.circuits import Circuit
from qcware_transpile.instructions import Instruction
from qsharp import compile
import tempfile
import parse


@composite
def gates(draw, num_qubits, gate_list=sorted(dialect().gate_defs)):
    gate_def = draw(
        sampled_from(gate_list).filter(lambda x: len(x.qubit_ids) <= num_qubits)
    )
    qubits = draw(
        lists(
            integers(min_value=0, max_value=num_qubits - 1),
            min_size=len(gate_def.qubit_ids),
            max_size=len(gate_def.qubit_ids),
            unique=True,
        )
    )
    kwargs = {}
    angles = floats(min_value=0, max_value=2 * math.pi)
    for p in gate_def.parameter_names:
        value = draw(angles)
        kwargs[p] = value
    result = Instruction(
        gate_def=gate_def, bit_bindings=qubits, parameter_bindings=kwargs
    )
    return result


@composite
def circuits(draw, min_qubits, max_qubits, min_length, max_length):
    length = draw(integers(min_value=min_length, max_value=max_length))
    num_qubits = draw(integers(min_value=min_qubits, max_value=max_qubits))
    circuit_gates = draw(lists(gates(num_qubits), min_size=length, max_size=length))
    circuit = Circuit.from_instructions(circuit_gates)
    result = ir_to_native(circuit)
    return result


def parse_dump_machine(lines):
    p = parse.compile("∣{:d}❭:\t{:g} + {:g} i")
    entries = [p.search(line) for line in lines if p.search(line) is not None]
    values = [complex(entry[1], entry[2]) for entry in entries]
    return numpy.array(values)


def run_generated_circuit(qc):
    ops = {x._name: x for x in compile(qc)}
    with tempfile.NamedTemporaryFile(mode="w+") as f:
        ops["DumpToFile"].simulate(filename=f.name)
        lines = f.readlines()
        result = parse_dump_machine(lines)
    return result


def measure_circuit(qc: str, shots: int):
    ops = {x._name: x for x in compile(qc)}
    num_qubits = len(ops["Measure"].simulate())
    result = {
        str(list(p)).replace(" ", ""): 0.0 for p in product(range(2), repeat=num_qubits)
    }
    for i in range(shots):
        x = ops["Measure"].simulate()
        result[str(x).replace(" ", "")] += 1
    for k, v in result.items():
        result[k] = v / shots
    return result
