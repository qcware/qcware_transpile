"""
Files for defining gates, gate definitions, and the like
"""
from pyrsistent import (pmap, pvector, pset, PMap, PSet, PVector)
from typing import Set, List, Union, Mapping, Optional, Dict, Sequence
from dpcontracts import require
from .helpers import (map_seq_to_seq)
import attr


def _qubit_ids(qubits: Union[int, Sequence[int]]):
    return pvector(range(qubits)) if isinstance(qubits,
                                                int) else pvector(qubits)


@attr.s(frozen=True)
class GateDef(object):
    """
    A gate definition, consisting only of a name, a set of names
    for parameters, and an ordered collection of integer qubit IDs
    """
    name = attr.ib(type=str)
    parameter_names = attr.ib(type=Set[str], converter=pset)
    qubit_ids = attr.ib(type=Sequence[int], converter=_qubit_ids)


@attr.s(frozen=True)
class Dialect(object):
    """
    A "dialect" -- essentially just a named set of gate definitions
    """
    name = attr.ib(type=str)
    gate_defs = attr.ib(type=PSet, converter=pset)


@attr.s(frozen=True)
class Instruction(object):
    """
    An instruction: a gate definition paired with parameter bindings
    and bit bindings
    """
    gate_def = attr.ib(type=GateDef)
    bit_bindings = attr.ib(type=Sequence[int], converter=_qubit_ids)
    parameter_bindings = attr.ib(type=Optional[Mapping],
                                 default=pmap(),
                                 converter=pmap)

    @parameter_bindings.validator
    def check_parameter_bindings(self, attribute, value):
        if not set(value.keys()).issubset(self.gate_def.parameter_names):
            raise ValueError(
                "parameter bindings must bind parameters in the gate def"
            )

    @bit_bindings.validator
    def check_bit_bindings(self, attribute, value):
        if len(value) != len(self.gate_def.qubit_ids):
            raise ValueError(
                "number of bit bindings must be equal to #bits in the gate def"
            )


def bit_bindings_map(instruction: Mapping) -> PMap:
    """
    Returns a "binding map" of bit ids to bit assignments;
    in other words, an instruction binding the gate CX with
    bit ids 0 and 1 to circuit bits 7 and 8 would return
    the map {0:7, 1:8}
    """
    qubit_ids = instruction.gate_def.qubit_ids
    bit_assignments = instruction.bit_bindings
    return map_seq_to_seq(qubit_ids, bit_assignments)


def circuit_bit_bindings(circuit: Mapping) -> PMap:
    """
    Given a sequence of instructions, return the complete
    map of bit bindings.  So "H(1), CX(0,1)" would return
    the bit bindings { (1,0):1, (2,0):0, (2,1):1 }
    """
    result = {}
    for i, instruction in enumerate(circuit.instructions):
        for k, v in bit_bindings_map(instruction).items():
            result[(i, k)] = v
    return pmap(result)


@attr.s(frozen=True)
class Circuit(object):
    dialect_name = attr.ib(type=str)
    instructions = attr.ib(type=Sequence[Instruction], converter=pvector)


def circuit_bit_binding_signature(c):
    pass
