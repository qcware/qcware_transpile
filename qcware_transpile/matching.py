"""
Files for defining gates, gate definitions, and the like
"""
from dpcontracts import require, ensure  # type: ignore
import attr
from pyrsistent.typing import PSet
from pyrsistent import pset
from typing import Callable, Optional
from .instructions import Instruction, remapped_instruction
from .gates import Dialect, GateDef
from .circuits import (Circuit, circuit_bit_targets,
                       circuit_is_valid_replacement,
                       circuit_is_valid_executable,
                       circuit_pattern_matches_target, circuit_parameter_map,
                       circuit_conforms_to_dialect, circuit_parameter_names)


@attr.s(frozen=True)
class TranslationRule(object):
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
        if not circuit_is_valid_replacement(self.replacement):
            raise ValueError(
                "Replacement circuit must be a valid replacement (fully bound with replacement-style parameter values)"
            )
        pattern_parameters = circuit_parameter_names(self.pattern)
        pm_replacement = circuit_parameter_map(self.replacement)
        pattern_keys = [
            x for x in pm_replacement.values() if isinstance(x, tuple)
        ]
        if not set(pattern_keys).issubset(pattern_parameters):
            raise ValueError(
                "Some replacement values reference tuples not in the source pattern"
            )

    def __str__(self):
        return "\n->\n".join([str(self.pattern), str(self.replacement)])


@require("Gates must have the same number of qubits",
         lambda args: len(args.a.qubit_ids) == len(args.b.qubit_ids))
@require("Only one parameter is allowed for trivial bindings",
         lambda args: len(args.a.parameter_names) == len(
             args.b.parameter_names) and len(args.a.parameter_names) <= 1)
@require("Argument gatedefs must belong to referenced dialects",
         lambda args: args.a in args.dialect_a.gate_defs and args.b in args.
         dialect_b.gate_defs)
def trivial_rule(dialect_a: Dialect,
                 a: GateDef,
                 dialect_b: Dialect,
                 b: GateDef,
                 f: Optional[Callable] = None) -> TranslationRule:
    """
    Create a trivial translation rule between two gate definitions,
    optionally with a translation lambda for the single parameter.  
    Unlike the target translation function, which takes the single
    parameter of a parameter map (which one would dereference for 
    actual arguments, ie "lambda pm: pm[(0,'theta')]*2") this takes
    a single value and returns a modified value, presuming that there
    single parameter shared by both gates is the same type

    This requires two gatedefs with the same number of qubits and
    up to one parameter.  Beyond that you'll have to be a bit more clever.
    """
    num_qubits = len(a.qubit_ids)
    pattern_instruction = Instruction(gate_def=a,
                                      bit_bindings=range(num_qubits),
                                      parameter_bindings={})
    if len(a.parameter_names) == 1:
        a_parameter_name = list(a.parameter_names)[0]
        b_parameter_name = list(b.parameter_names)[0]

        b_parameter_target = (0, a_parameter_name)
        b_parameter_value = b_parameter_target if f is None else lambda pm: f(
            pm[b_parameter_target])
        parameter_bindings = {b_parameter_name: b_parameter_value}
    else:
        parameter_bindings = {}
    target_instruction = Instruction(
        gate_def=b,
        bit_bindings=range(num_qubits),
        parameter_bindings=parameter_bindings)  # type: ignore
    return TranslationRule(
        pattern=Circuit.from_instructions(dialect_a.name,
                                          [pattern_instruction]),
        replacement=Circuit.from_instructions(dialect_b.name,
                                              [target_instruction]))


@require("translation pattern must match circuit", lambda args:
         circuit_pattern_matches_target(args.translation.pattern, args.target))
@require("target circuit must be executable",
         lambda args: circuit_is_valid_executable(args.target))
def translation_replace_circuit(translation: TranslationRule,
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
        for i in translation.replacement.instructions  # was target
    ]
    # hmm, ignoring the following because it raised a curious
    # error: Argument "instructions" to "Circuit" has incompatible
    # type "List[Instruction]"; expected "Iterable[T]"
    return Circuit.from_instructions(
        dialect_name=translation.replacement.dialect_name,
        instructions=replacement_instructions)  # type: ignore


@attr.s
class TranslationSet(object):
    """
    A TranslationSet is a translation between one Dialect and another.
    """
    from_dialect = attr.ib(type=Dialect)
    to_dialect = attr.ib(type=Dialect)
    rules = attr.ib(type=PSet[TranslationRule], converter=pset)

    def __str__(self):
        return "\n  ".join(
            ["->".join([self.from_dialect.name, self.to_dialect.name])] +
            [str(rule) for rule in self.rules])


def matching_rules(ts: TranslationSet, c: Circuit) -> PSet[TranslationRule]:
    """
    The set of rules from the translation set which match the circuit.
    Right now this is not efficient; it could be assisted by maps based on
    first gate name in the rule, etc.
    """
    return pset(
        {r
         for r in ts.rules if circuit_pattern_matches_target(r.pattern, c)})


def circuit_is_simply_translatable_by(c: Circuit, ts: TranslationSet) -> bool:
    """
    A simple translation is one where each instruction in the circuit is
    addressed by a single-instruction pattern in the translation set
    """
    subcircuits = [
        Circuit.from_instructions(c.dialect_name, [i]) for i in c.instructions
    ]  # type: ignore
    return all([len(matching_rules(ts, subc)) > 0 for subc in subcircuits])


@require("Circuit must belong to the translation set 'from' dialect",
         lambda args: args.target.dialect_name == args.ts.from_dialect.name)
@require(
    "Circuit must be fully translatable by a single rule in the translation set",
    lambda args: len(matching_rules(args.ts, args.target)) > 0)
def translationset_replace_circuit(ts: TranslationSet,
                                   target: Circuit) -> Circuit:
    """
    Compute a replacement circuit by the given translation set
    """
    # choose an arbitrary matching rule
    rule = list(matching_rules(ts, target))[0]
    return translation_replace_circuit(rule, target)


@require("Circuit must belong to the translation set 'from' dialect",
         lambda args: circuit_conforms_to_dialect(args.c, args.ts.from_dialect)
         )
@require("Circuit must be simply translatable by the translation set",
         lambda args: circuit_is_simply_translatable_by(args.c, args.ts))
@ensure("Result must belong to the translation set 'to' dialect",
        lambda args, result: circuit_conforms_to_dialect(
            result, args.ts.to_dialect))
def simple_translate(ts: TranslationSet, c: Circuit) -> Circuit:
    """
    Given a simple translation set ts, breaks c into subcircuits
    of length 1 (ie individual instructions), translates each instruction,
    and assembles the result into a circuit belonging to the target
    dialect
    """
    subcircuits = [
        Circuit.from_instructions(c.dialect_name, [i]) for i in c.instructions
    ]  # type: ignore
    new_instructions = [
        instruction for sub in subcircuits
        for instruction in translationset_replace_circuit(ts, sub).instructions
        for sub in subcircuits
    ]
    return Circuit.from_instructions(dialect_name=c.dialect_name,
                                     instructions=new_instructions)
