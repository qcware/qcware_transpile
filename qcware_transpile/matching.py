"""
Files for defining gates, gate definitions, and the like
"""
from pyrsistent import (pmap, pvector, pset)
from pyrsistent.typing import (PMap, PSet, PVector)
from typing import Set, List, Union, Mapping, Optional, Dict, Sequence, Tuple, Any
from dpcontracts import require  # type: ignore
from .helpers import (map_seq_to_seq, reverse_map)
import attr
from inspect import signature


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
    bound to values, not functions.  This is important in deciding if a 
    circuit is fully bound (a target for a match pattern)
    or only a pattern (only a subset of 
    parameters is bound), or a match target (some parameters are bound
    to callables)
    """
    return all([(k in i.parameter_bindings
                 and (not callable(i.parameter_bindings[k])))
                for k in i.gate_def.parameter_names])


def _is_valid_executable_parameter_value(v: Any) -> bool:
    """
    whether the instruction parameter is valid for execution (is numeric)
    """
    return type(v) in {int, float, complex}


def _is_valid_replacement_parameter_value(v: Any) -> bool:
    """
    Determines if a given value is a valid replacement
    parameter, ie if it is a tuple, callable of one argument,
    or numeric parameter
    """
    return ((isinstance(v, tuple) and isinstance(v[0], int)
             and isinstance(v[1], str))
            or (callable(v) and len(signature(v).parameters) == 1)
            or (type(v) in {int, float, complex}))


def instruction_is_valid_executable(i: Instruction) -> bool:
    """
    An instruction is a valid executable instruction if it is
    fully bound and if all parameter values are concrete
    numbers
    """
    return (instruction_parameters_are_fully_bound(i) and all([
        _is_valid_executable_parameter_value(v)
        for v in i.parameter_bindings.values()
    ]))


def instruction_is_valid_replacement(i: Instruction) -> bool:
    """
    An instruction is a valid replacement instruction if it is
    fully bound and if all parameter "values" are either a
    value, tuple, or callable of one argument
    """
    return (instruction_parameters_are_fully_bound(i) and all([
        _is_valid_replacement_parameter_value(v)
        for v in i.parameter_bindings.values()
    ]))


def instruction_parameter_bindings_match(pattern: Instruction,
                                         target: Instruction) -> bool:
    """
    the parameters of an instruction "pattern" matches a target if all
    bound parameters in the pattern have keys present in the target
    and the bound values are the same
    """
    return set(pattern.parameter_bindings.keys()).issubset(
        set(target.parameter_bindings.keys())) \
        and all([pattern.parameter_bindings[x]
               == target.parameter_bindings[x]
               for x in pattern.parameter_bindings.keys()])


def instruction_pattern_matches_target(pattern: Instruction,
                                       target: Instruction) -> bool:
    """
    An instruction pattern matches a target if it has the same gate name,
    and matching parameter bindings
    """
    return ((pattern.gate_def.name == target.gate_def.name)
            and instruction_parameter_bindings_match(pattern, target))


def instruction_bit_bindings_map(
        instruction: Instruction) -> PMap[int, Set[int]]:
    """
    Returns a "binding map" of bit ids to bit assignments;
    in other words, an instruction binding the gate CX with
    bit ids 0 and 1 to circuit bits 7 and 8 would return
    the map {0:7, 1:8}
    """
    qubit_ids = instruction.gate_def.qubit_ids
    bit_assignments = instruction.bit_bindings
    return map_seq_to_seq(qubit_ids, bit_assignments)


def _remapped_parameter(parameter_map: Mapping[Tuple[int, str], Any],
                        parameter_value: Any):
    """
    Remaps a parameter in a match target.  There are three
    options for a match target value:

    * If the value is a callable, call it, passing the parameter
      map as the argument
    * If the value is a tuple, replace it with the appropriate
      value from the parameter map
    * Otherwise, just keep the original value
    """
    if callable(parameter_value):
        result = parameter_value(parameter_map)
    elif isinstance(parameter_value, tuple):
        # ignoring type here as we *should* have a
        # value of type (int, str)->number
        result = parameter_map[parameter_value]  # type: ignore
    else:
        result = parameter_value
    return result


def remapped_instruction(qubit_map: Mapping[int, int],
                         parameter_map: Mapping[Tuple[int, str], Any],
                         target: Instruction) -> Instruction:
    """
    This remaps an instruction given a new qubit mapping (from
    target qubits in one circuit to target qubits in another) and
    a new parameter map (from the parameters in the original circuit,
    ie the keys in the parameter map are tuples of (index, parameter_name)

    """
    new_parameters = {
        # ignoring type as the following seems to confuse it; v can
        # either be a key into the parameter map or a tuple
        k: _remapped_parameter(parameter_map, v)
        for k, v in target.parameter_bindings.items()
    }
    new_bit_bindings = [qubit_map[b] for b in target.bit_bindings]
    return Instruction(gate_def=target.gate_def,
                       parameter_bindings=new_parameters,
                       bit_bindings=new_bit_bindings)


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


@attr.s
class Translation(object):
    """
    A translation: a map from one circuit to another.  The replacement
    must be a fully-bound circuit (all parameters for all instructions
    must be bound) with the same set of input bits as the pattern
    """
    pattern = attr.ib(type=Circuit)
    replacement = attr.ib(type=Circuit)

    @replacement.validator
    def check_replacement(self, attribute, value):
        # replacement must address the same bits as pattern
        pattern_bits = circuit_bit_targets(self.pattern)
        replacement_bits = circuit_bit_targets(self.replacement)
        if pattern_bits != replacement_bits:
            raise ValueError(
                "pattern and replacement must target the same set of bits")
        # replacement values must either be values or keys into pattern
        if not circuit_is_valid_replacement(c):
            raise ValueError(
                "Replacement circuit must be a valid replacement (fully bound with replacement-style parameter values)"
            )
        pm_pattern = circuit_parameter_map(self.pattern)
        pm_replacement = circuit_parameter_map(self.replacement)
        pattern_keys = [
            x for x in pm_replacement.values() if isinstance(x, tuple)
        ]
        if not set(pattern_keys).issubset(set(pm_pattern.keys())):
            raise ValueError(
                "Some replacement values reference tuples not in the source pattern"
            )

    def __str__(self):
        return "\n->\n".join([str(self.pattern), str(self.replacement)])


@require("translation pattern must match circuit", lambda args:
         circuit_pattern_matches_target(args.translation.pattern, args.target))
@require("target circuit must be executable",
         lambda args: circuit_is_valid_executable(args.circuit))
def translation_replace_circuit(translation: Translation,
                                target: Circuit) -> Circuit:
    pattern_bits = list(circuit_bit_targets(translation.pattern))
    target_bits = list(circuit_bit_targets(target))
    qubit_map = {
        pattern_bits[i]: target_bits[i]
        for i in range(len(pattern_bits))
    }
    parameter_map = circuit_parameter_map(target)
    replacement_instructions = [
        remapped_instruction(qubit_map, parameter_map, i)
        for i in target.instructions
    ]
    # hmm, ignoring the following because it raised a curious
    # error: Argument "instructions" to "Circuit" has incompatible
    # type "List[Instruction]"; expected "Iterable[T]"
    return Circuit(dialect_name=translation.replacement.dialect_name,
                   instructions=replacement_instructions)  # type: ignore
