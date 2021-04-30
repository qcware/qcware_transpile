import math
from hypothesis.strategies import (composite, floats, integers, lists, sampled_from)
from jinja2 import Template
from qcware_transpile.dialects.qsharp.qsharp_dialect import dialect

@composite
def gates(draw, 
          min_qubits, 
          max_qubits,
          gate_list=sorted(dialect().gate_defs)):
    num_qubits = draw(integers(min_value=min_qubits, max_value=max_qubits))
    gate_def = draw(sampled_from(gate_list).filter(lambda x: len(x.qubit_ids) <= num_qubits))
    qubits = draw(
            lists(integers(min_value=0, max_value=num_qubits-1), 
                  min_size=len(gate_def.qubit_ids), 
                  max_size=len(gate_def.qubit_ids), 
                  unique=True))
    qubit_str = ", ".join("q[%d]" % (q) for q in qubits)
    result = gate_def.name + "(" + qubit_str + ")"
    if gate_def.parameter_names:
        angles = draw(
            lists(floats(min_value=0, max_value=2 * math.pi), 
                        min_size=len(gate_def.parameter_names), 
                        max_size=len(gate_def.parameter_names)))
        param_str = ", ".join("%s" % (a) for a in angles)
        result = gate_def.name + "(" + param_str + ", " + qubit_str + ")"  
    return result 