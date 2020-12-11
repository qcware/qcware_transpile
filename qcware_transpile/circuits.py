import attr
from typing import Set, Tuple, Sequence, Mapping, Any
from pyrsistent import pvector, pmap, pset
from pyrsistent.typing import PMap, PSet
from dpcontracts import require # type: ignore
from .helpers import reverse_map
from .instructions import (Instruction, instruction_bit_bindings_map,
                           instruction_parameters_are_fully_bound,
                           instruction_is_valid_executable,
                           instruction_is_valid_replacement,
                           instruction_pattern_matches_target)


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
        for k, v in instruction_bit_bindings_map(instruction).items():
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


def circuit_is_valid_executable(c: Circuit) -> bool:
    """
    Whether not each instruction in the circuit is executable
    """
    return all([instruction_is_valid_executable(i) for i in c.instructions])


def circuit_is_valid_replacement(c: Circuit) -> bool:
    """
    Whether or not each instruction in the circuit is a valid replacement
    """
    return all([instruction_is_valid_replacement(i) for i in c.instructions])


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


def circuit_parameter_map(c: Circuit) -> Mapping[Tuple[int, str], Any]:
    result = {}
    for index, i in enumerate(c.instructions):
        for k, v in i.parameter_bindings.items():
            result[(index, k)] = v
    return pmap(result)


def circuit_bit_targets(c: Circuit) -> PSet[int]:
    """
    The set of bits targeted by this circuit (the set
    of bits this circuit's instructions are bound to)
    """
    return pset(set().union(*[i.bit_bindings
                              for i in c.instructions]))  # type: ignore