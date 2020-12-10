"""
Files for defining gates, gate definitions, and the like
"""
from pyrsistent import (pmap, pvector, pset)
from pyrsistent.typing import (PMap, PSet, PVector)
from typing import Set, List, Union, Mapping, Optional, Dict, Sequence, Tuple
from dpcontracts import require  # type: ignore
from .helpers import (map_seq_to_seq, reverse_map)
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


@attr.s()
class Dialect(object):
    """
    A "dialect" -- essentially just a named set of gate definitions
    """
    name = attr.ib(type=str)
    gate_defs = attr.ib(type=PSet, converter=pset)


@attr.s()
class Instruction(object):
    """
    An instruction: a gate definition paired with parameter bindings
    and bit bindings
    """
    gate_def = attr.ib(type=GateDef)
    bit_bindings = attr.ib(type=PVector[int], converter=_qubit_ids)
    parameter_bindings = attr.ib(type=Mapping, default=pmap(), converter=pmap)

    @parameter_bindings.validator
    def check_parameter_bindings(self, attribute, value):
        if not set(value.keys()).issubset(self.gate_def.parameter_names):
            raise ValueError(
                "parameter bindings must bind parameters in the gate def")

    @bit_bindings.validator
    def check_bit_bindings(self, attribute, value):
        if len(value) != len(self.gate_def.qubit_ids):
            raise ValueError(
                "number of bit bindings must be equal to #bits in the gate def"
            )

    def __str__(self):
        parameter_bindings_str = ",".join(
            [f"{k}={v}" for k, v in self.parameter_bindings.items()])
        bit_bindings_str = ",".join([f"{x}" for x in self.bit_bindings])
        return f"{self.gate_def.name}({parameter_bindings_str}), ({bit_bindings_str}))"


def instruction_parameters_are_fully_bound(i: Instruction) -> bool:
    """
    Whether or not all parameters in the instruction are fully
    bound to values.  This is important in deciding if a 
    circuit is fully bound (a target for a match pattern)
    or only a pattern (only a subset of 
    parameters is bound)
    """
    # ignoring the type error below because parameter_bindings
    # is set to PMap as default
    return set(i.gate_def.parameter_names) == set(
        i.parameter_bindings.keys())  # type: ignore


def instruction_parameter_bindings_match(pattern: Instruction,
                                         target: Instruction) -> bool:
    """
    the parameters of an instruction "pattern" matches a target if all
    bound parameters in the pattern have keys present in the target
    and the bound values are the same
    """
    return set(pattern.parameter_bindings.keys()).issubset(set(target.parameter_bindings.keys())) \
        and all([pattern.parameter_bindings[x] == target.parameter_bindings[x] for x in pattern.parameter_bindings.keys()])


def instruction_pattern_matches_target(pattern: Instruction,
                                       target: Instruction) -> bool:
    """
    An instruction pattern matches a target if it has the same gate name,
    and matching parameter bindings
    """
    return ((pattern.gate_def.name == target.gate_def.name)
            and instruction_parameter_bindings_match(pattern, target))


def bit_bindings_map(instruction: Instruction) -> PMap[int, Set[int]]:
    """
    Returns a "binding map" of bit ids to bit assignments;
    in other words, an instruction binding the gate CX with
    bit ids 0 and 1 to circuit bits 7 and 8 would return
    the map {0:7, 1:8}
    """
    qubit_ids = instruction.gate_def.qubit_ids
    bit_assignments = instruction.bit_bindings
    return map_seq_to_seq(qubit_ids, bit_assignments)


@attr.s()
class Circuit(object):
    dialect_name = attr.ib(type=str)
    instructions = attr.ib(type=Sequence[Instruction], converter=pvector)

    def __str__(self):
        return "\n".join([self.dialect_name] +
                         [str(i) for i in self.instructions])


def circuit_bit_bindings(circuit: Circuit) -> PMap[Tuple[int, int], Set[int]]:
    """
    Given a sequence of instructions, return the complete
    map of bit bindings.  So "H(1), CX(0,1)" would return
    the bit bindings { (1,0):1, (2,0):0, (2,1):1 }
    """
    result: dict = {}
    for i, instruction in enumerate(circuit.instructions):
        for k, v in bit_bindings_map(instruction).items():
            result[(i, k)] = v
    return pmap(result)


"""
A BitBindingSignature is a type declaration here, but it's
"the set of sets of bit IDs in the circuit instructions which are bound to the
same bit"

So {{(0,0), (1,0)}, {(0,1)}} means that for a two-instruction circuit,
both instruction 0, bit 0 and instruction 1 bit 1 are bound to the same input
bit, and instruction 0, bit 1 is bound to a different bit.

The BitBindingSignature is used to compare two circuits and see if they have
the same basic graph structure
"""
BitBindingSignature = PSet[PSet[Tuple[int, int]]]


def circuit_bit_binding_signature(c: Circuit) -> BitBindingSignature:
    """
    Create the BitBindingSignature of a circuit
    """
    forward_bindings = circuit_bit_bindings(c)
    reverse_bindings = reverse_map(forward_bindings)
    return pset(reverse_bindings.values())


def circuit_parameters_are_fully_bound(c: Circuit) -> bool:
    """
    Whether or not every instruction in the circuit has its parameters
    fully bound
    """
    return all(
        [instruction_parameters_are_fully_bound(i) for i in c.instructions])


@require("both pattern and target must have the same number of instructions",
         lambda args: len(args.pattern.instructions) == len(args.target.
                                                            instructions))
@require("parameters in target must be fully bound",
         lambda args: circuit_parameters_are_fully_bound(args.target))
def circuit_pattern_matches_target(pattern: Circuit, target: Circuit) -> bool:
    return ((len(pattern.instructions) == len(target.instructions)) and all([
        instruction_pattern_matches_target(pattern.instructions[i],
                                           target.instructions[i])
        for i in range(len(pattern.instructions))
    ]) and (circuit_bit_binding_signature(pattern)
            == circuit_bit_binding_signature(target)))
