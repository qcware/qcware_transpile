"""
Files for defining gates, gate definitions, and the like
"""
from pyrsistent import pmap, pvector, pset
from typing import Set, List, Union, Mapping, Optional
from dpcontracts import require
from .helpers import map_seq_to_seq


def gate_def(name: str,
             bits: Union[int, List[int]],
             parameter_names: Optional[Set[str]] = None):
    bit_ids = pvector(range(bits)) if isinstance(bits, int) else pvector(bits)
    parameter_names = pset(
        []) if parameter_names is None else pset(parameter_names)
    return pmap({
        "name": name,
        "parameter_names": parameter_names,
        "bit_ids": bit_ids
    })


@require("names in parameter_bindings must be a subset of those in gatedef",
         lambda args: set(args.parameter_bindings.keys()).issubset(
             args.gatedef.parameter_names))
@require(
    "number of bit bindings must be equal to number of bits for the gatedef",
    lambda args: len(args.bit_bindings) == len(args.gatedef.bit_ids))
def instruction(gatedef: Mapping,
                bit_bindings: List,
                parameter_bindings: Optional[Mapping] = pmap()):
    return pmap({
        "gatedef": pmap(gatedef),
        "parameter_bindings": pmap(parameter_bindings),
        "bit_bindings": pvector(bit_bindings)
    })


def bit_bindings_map(instruction: Mapping):
    """
    Returns a "binding map" of bit ids to bit assignments
    """
    bit_ids = instruction['gatedef']['bit_ids']
    bit_assignments = instruction['bit_bindings']
    return map_seq_to_seq(bit_ids, bit_assignments)

