from hypothesis.strategies import (composite, integers, text, lists,
                                   sampled_from)
from qcware_transpile.matching import gate_def, instruction
from typing import Set
import string


@composite
def gate_defs(draw,
              names=text(alphabet=list(string.ascii_uppercase),
                         min_size=1,
                         max_size=3),
              num_bits=integers(min_value=1, max_value=3),
              parameter_names=text(alphabet=list(string.ascii_lowercase),
                                   min_size=3,
                                   max_size=5)):
    """
    Create a random gate definition; used to create arbitrary dialects
    """
    return gate_def(draw(names), draw(num_bits),
                    draw(lists(parameter_names, min_size=1, max_size=3)))


@composite
def instructions(draw,
                 gate_defs: Set,
                 min_qubit=0,
                 max_qubit=5,
                 min_parameter=0,
                 max_parameter=100):
    """
    Create a random gate definition; requires a fixed list of gate definitions
    (rather than a the gate_defs strategy) so you don't simply get a bunch of
    garbage.
    """
    gatedef = draw(sampled_from(gate_defs))
    parameter_bindings = {
        parameter:
        draw(integers(min_value=min_parameter, max_value=max_parameter))
        for parameter in gatedef['parameter_names']
    }
    bit_bindings = draw(
        lists(integers(min_value=min_qubit, max_value=max_qubit),
              min_size=len(gatedef.bit_ids),
              max_size=len(gatedef.bit_ids)))
    return instruction(gatedef, bit_bindings, parameter_bindings)
