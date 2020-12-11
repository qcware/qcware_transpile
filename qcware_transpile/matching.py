"""
Files for defining gates, gate definitions, and the like
"""
from dpcontracts import require  # type: ignore
import attr
from .instructions import remapped_instruction
from .circuits import (Circuit, circuit_bit_targets,
                       circuit_is_valid_replacement,
                       circuit_is_valid_executable,
                       circuit_pattern_matches_target,
                       circuit_parameter_map)


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
        if not circuit_is_valid_replacement(self.replacement):
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
