"""Functions and data structures for marshaling to/from
wire-compatible data structures (python dicts, json,
etc.)
"""
from icontract import require

from qcware_transpile.circuits import Circuit
from qcware_transpile.gates import Dialect, GateDef
from qcware_transpile.instructions import Instruction


def circuit_to_dict(c: Circuit) -> dict:
    """
    Transforms the circuit to a regular dict suitable for JSON
    """
    return dict(
        dialect_name=c.dialect_name,
        instructions=[instruction_to_dict(i) for i in c.instructions],
        qubits=list(c.qubits),
    )


@require(lambda d, dialect: dialect.name == d["dialect_name"])
def dict_to_circuit(d: dict, dialect: Dialect) -> Circuit:
    """Transforms the dict into a circuit object using the set dialect"""
    return Circuit(
        dialect_name=d["dialect_name"],
        instructions=[
            dict_to_instruction(i, dialect) for i in d["instructions"]  # type:ignore
        ],
        qubits=d["qubits"],
    )


def instruction_to_dict(i: Instruction) -> dict:
    """
    Dict representation of an instruction, suitable for JSON
    """
    return dict(
        gate=i.gate_def.name,
        bits=list(i.bit_bindings),
        parameters=dict(i.parameter_bindings),
        metadata=dict(i.metadata),
    )


@require(lambda d, dialect: dialect.has_gate_named(d["gate"]))
def dict_to_instruction(d: dict, dialect: Dialect) -> Instruction:
    return Instruction(
        gate_def=dialect.gate_named(d["gate"]),
        bit_bindings=d["bits"],
        parameter_bindings=d["parameters"],
        metadata=d["metadata"],
    )
