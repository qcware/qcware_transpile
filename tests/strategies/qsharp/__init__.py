import math
import numpy 
from hypothesis import given, settings
from hypothesis.strategies import (composite, floats, integers, lists,
                                   sampled_from)
from jinja2 import Template
from qcware_transpile.dialects.qsharp.qsharp_dialect import dialect
from qsharp import compile
import tempfile
import parse

@composite
def gates(draw, num_qubits, gate_list=sorted(dialect().gate_defs)):
    gate_def = draw(
        sampled_from(gate_list).filter(
            lambda x: len(x.qubit_ids) <= num_qubits))
    qubits = draw(
        lists(integers(min_value=0, max_value=num_qubits - 1),
              min_size=len(gate_def.qubit_ids),
              max_size=len(gate_def.qubit_ids),
              unique=True))
    qubit_str = ", ".join("qs[%d]" % (q) for q in qubits)
    result = gate_def.name + "(" + qubit_str + ")"
    if gate_def.parameter_names:
        angles = draw(
            lists(floats(min_value=0, max_value=2 * math.pi),
                  min_size=len(gate_def.parameter_names),
                  max_size=len(gate_def.parameter_names)))
        param_str = ", ".join("%s" % (a) for a in angles)
        result = gate_def.name + "(" + param_str + ", " + qubit_str + ")"
    return result


@composite
def circuits(draw, min_qubits, max_qubits, min_length, max_length):
    length = draw(integers(min_value=min_length, max_value=max_length))
    num_qubits = draw(integers(min_value=min_qubits, max_value=max_qubits))
    circuit_gates = draw(
        lists(gates(num_qubits), min_size=length, max_size=length))
    result = Template("""
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Diagnostics as Diagnostics;

    operation TestCircuit(): Unit {

        use qs = Qubit[{{num_qubits}}];

        Message("Initial state |000>:");

        {% for gate in circuit_gates %} 
        {{gate}}; 
        {% endfor %}

        Message("After:");
        Diagnostics.DumpMachine("{{ output_file }}");

        ResetAll(qs);
    }
    """)
    return result.render(num_qubits=num_qubits, circuit_gates=circuit_gates, output_file="{{ output_file }}")


def parse_dump_machine(lines):
    p = parse.compile("∣{:d}❭:\t{:g} + {:g} i")
    entries = [p.search(line) for line in lines if p.search(line) is not None]
    values = [complex(entry[1], entry[2]) for entry in entries]
    return numpy.array(values)

def run_generated_circuit(qc_nooutput):
    with tempfile.NamedTemporaryFile(mode="w+") as f:
        qc = Template(qc_nooutput).render(output_file=f.name)
        compile(qc).simulate()
        lines = f.readlines()
        result = parse_dump_machine(lines)
    return result


ex = circuits(2,3,2,3).example()
run_generated_circuit(ex)