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
    # and Microsoft.Quantum.Canon libraries
    simple_gates: Tuple[Tuple[str, Set, int]] = (
        ("CCNOT", set(), 3),
        ("CNOT", set(), 2),
        ("H", set(), 1),
        ("I", set(), 1),
        ("Rx", {"theta"}, 1),
        ("Ry", {"theta"}, 1),
        ("Rz", {"theta"}, 1),
        ("S", set(), 1),
        ("SWAP", set(), 2),
        ("T", set(), 1),
        ("X", set(), 1),
        ("Y", set(), 1),
        ("Z", set(), 1),
        ("R1", {"theta"}, 1),
        ("CY", {}, 2),
        ("CZ", {}, 2),
    )  # type: ignore
    return pset({simple_gate(t) for t in simple_gates})


def dialect() -> Dialect:
    return Dialect(name=__dialect_name__, gate_defs=gate_defs())  # type: ignore


def qsharp_operation_from_instruction(i: Instruction) -> str:
    qubit_str = ", ".join("qs[%d]" % (q) for q in i.bit_bindings)
    operation = i.gate_def.name + "(" + qubit_str + ")"
    if i.parameter_bindings:
        param_str = ", ".join("%s" % (v) for k, v in i.parameter_bindings.items())
        operation = i.gate_def.name + "(" + param_str + ", " + qubit_str + ")"
    return operation


def ir_to_native(c: Circuit) -> str:
    operations = []
    for instruction in c.instructions:
        operations.append(qsharp_operation_from_instruction(instruction))

    result = Template(
        """
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Diagnostics as Diagnostics;

    operation PrepareState(qs: Qubit[]): Unit {

        {% for operation in operations %}{{operation}};
        {% endfor %}

    }

    operation DumpToFile(filename: String): Unit {

        use qs = Qubit[{{num_qubits}}];
        PrepareState(qs);
        Diagnostics.DumpMachine(filename);
        ResetAll(qs);
    }

    operation Measure(): Result[] {

        use qs = Qubit[{{num_qubits}}];
        PrepareState(qs);
        return MultiM(qs);

    }
    """
    )
    return result.render(num_qubits=max(c.qubits) + 1, operations=operations)
