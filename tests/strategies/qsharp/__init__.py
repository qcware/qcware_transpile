import math
from hypothesis import given, settings
from hypothesis.strategies import (composite, floats, integers, lists, sampled_from)
from jinja2 import Template
from qcware_transpile.dialects.qsharp.qsharp_dialect import dialect
from qsharp import compile
from qsharp.loader import QSharpCallable

@composite
def gates(draw, 
          num_qubits,
          gate_list=sorted(dialect().gate_defs)):
    gate_def = draw(sampled_from(gate_list).filter(lambda x: len(x.qubit_ids) <= num_qubits))
    qubits = draw(
            lists(integers(min_value=0, max_value=num_qubits-1), 
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
def circuits(draw, 
             min_qubits, 
             max_qubits, 
             min_length, 
             max_length):
    length = draw(integers(min_value=min_length, max_value=max_length))
    length = draw(integers(min_value=min_length, max_value=max_length))
    num_qubits = draw(integers(min_value=min_qubits, max_value=max_qubits))
    circuit_gates = draw(lists(gates(num_qubits), min_size=length, max_size=length))
    result = Template("""
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Diagnostics;

    operation TestCircuit(): Unit {

        use qs = Qubit[{{num_qubits}}];

        Message("Initial state |000>:");
        DumpMachine();

        {% for gate in circuit_gates %} 
        {{gate}}; 
        {% endfor %}

        Message("After:");
        DumpMachine();

        ResetAll(qs);
    }
    """)
    return result.render(num_qubits=num_qubits, circuit_gates=circuit_gates)

def run_generated_circuit(qc):
    return compile(qc).simulate()