"""
Files for defining gates, gate definitions, and the like
"""
from dpcontracts import require  # type: ignore
import attr
from pyrsistent.typing import PSet
from pyrsistent import pset
from .instructions import remapped_instruction
from .gates import Dialect
from .circuits import (Circuit, circuit_bit_targets,
                       circuit_is_valid_replacement,
                       circuit_is_valid_executable,
                       circuit_pattern_matches_target, circuit_parameter_map,
                       circuit_parameter_names)


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
    subcircuits = [Circuit.from_instructions(c.dialect_name, [i])
                   for i in c.instructions]  # type: ignore
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
         lambda args: args.c.dialect_name == args.ts.from_dialect.name)
@require("Circuit must be simply translatable by the translation set",
         lambda args: circuit_is_simply_translatable_by(args.c, args.ts))
def simple_translate(ts: TranslationSet, c: Circuit) -> Circuit:
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
