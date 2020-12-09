"""
Files for defining gates, gate definitions, and the like
"""
from pyrsistent import (pmap, pvector, pset, PMap)
from typing import Set, List, Union, Mapping, Optional, Dict, Sequence
from dpcontracts import require
from .helpers import (map_seq_to_seq)


def gate_def(name: str,
             bits: Union[int, List[int]],
             parameter_names: Optional[Set[str]] = None) -> PMap:
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
def instruction(
    gatedef: Mapping,
    bit_bindings: List,
    parameter_bindings: Optional[Mapping] = pmap()) -> PMap:
    return pmap({
        "gatedef": pmap(gatedef),
        "parameter_bindings": pmap(parameter_bindings),
        "bit_bindings": pvector(bit_bindings)
    })


def bit_bindings_map(instruction: Mapping) -> PMap:
    """
    Returns a "binding map" of bit ids to bit assignments;
    in other words, an instruction binding the gate CX with
    bit ids 0 and 1 to circuit bits 7 and 8 would return
    the map {0:7, 1:8}
    """
    bit_ids = instruction['gatedef']['bit_ids']
    bit_assignments = instruction['bit_bindings']
    return map_seq_to_seq(bit_ids, bit_assignments)


def circuit_bit_bindings(circuit: Sequence[Dict]) -> PMap:
    """
    Given a sequence of instructions, return the complete
    map of bit bindings.  So "H(1), CX(0,1)" would return
    the bit bindings { (1,0):1, (2,0):0, (2,1):1 }
    """
    result = {}
    for instruction, i in enumerate(circuit):
        for k, v in bit_bindings_map(instruction):
            result[(i, k)] = v
    return pmap(result)
