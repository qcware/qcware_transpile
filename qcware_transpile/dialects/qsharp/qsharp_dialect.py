"""
Unfortunately, Qsharp, being in a separate language and library,
doesn't lend itself to introspection, so our usual approach
to finding the possible gates and excluding problematic ones
will have to be the simpler but more labor-intensive route
of hard-coding them.

QSharp python docs: https://docs.microsoft.com/en-us/python/qsharp-core/qsharp
"""
from qcware_transpile.gates import GateDef, Dialect
from qcware_transpile.circuits import Circuit
from qcware_transpile.instructions import Instruction
from jinja2 import Template
from typing import Tuple, Set
from pyrsistent import pset
from pyrsistent.typing import PSet

__dialect_name__ = "qsharp"


def simple_gate(t: Tuple[str, set, int]):
    return GateDef(name=t[0], parameter_names=t[1], qubit_ids=t[2])


def gate_defs() -> PSet[GateDef]:
    # a list of basic gates.  Currently these come from the Microsoft.Quantum.Intrinsics
    # library
    simple_gates: Tuple[Tuple[str, Set,
                              int]] = (("CCNOT", set(), 3), ("CNOT", set(), 2),
                                       ("H", set(), 1), ("I", set(), 1),
                                       ("Rx", {"theta"}, 1), ("Ry", {"theta"},
                                                              1),
                                       ("Rz", {"theta"}, 1), ("S", set(), 1),
                                       ("SWAP", set(), 2), ("T", set(), 1),
                                       ("X", set(), 1), ("Y", set(), 1), ("Z", set(), 1), 
                                       ("R1", {"theta"}, 1), ("CY", {}, 2), ("CZ", {}, 2)) # type: ignore
    return pset({simple_gate(t) for t in simple_gates})


def dialect() -> Dialect:
    return Dialect(name=__dialect_name__, gate_defs=gate_defs()) # type: ignore

def ir_to_native(c: Circuit) -> str:
    operations = []
    for instruction in c.instructions:
        qubit_str = ", ".join("qs[%d]" % (q) for q in instruction.bit_bindings)
        operation = instruction.gate_def.name + "(" + qubit_str + ")"
        if instruction.parameter_bindings:
            param_str = ", ".join("%s" % (v) for k, v in instruction.parameter_bindings.items())
            operation = instruction.gate_def.name + "(" + param_str + ", " + qubit_str + ")"
        operations.append(operation)

    result = Template("""
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Diagnostics as Diagnostics;

    operation TestCircuit(): Unit {

        use qs = Qubit[{{num_qubits}}];

        Message("Initial state |000>:");

        {% for operation in operations %} 
        {{operation}}; 
        {% endfor %}

        Message("After:");
        Diagnostics.DumpMachine("{{ output_file }}");

        ResetAll(qs);
    }
    """)
    return result.render(num_qubits=max(c.qubits)+1, operations=operations, output_file="{{ output_file }}")


bellpair = Circuit.from_tuples(dialect(),
                               (("H", {}, [0]), ("CNOT", {}, [0, 1])))
