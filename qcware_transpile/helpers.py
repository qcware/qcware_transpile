"""
Some helper functions
"""
from typing import Sequence
from dpcontracts import require
from pyrsistent import pmap

@require("Sequences must be the same length",
         lambda args: len(args.s1) == len(args.s2))
def map_seq_to_seq(s1: Sequence, s2: Sequence):
    """
    Given two sequences of equal lengths, map each
    element of s1 to the set of the corresponding element in s2,
    such that domain(result) == set(s1); return the mapping
    as a pmap

    If s1 has multiple entries with equal values, the 
    results for f(x) would be {y,z...}; in other words,
    mapping [1,2,1] onto [3,4,5] would result in
    { 1: {3,5}, 2: {4} }
    """
    result = {}
    for i in range(len(s1)):
        x = s1[i]
        y = s2[i]
        if x in result:
            result[x].add(y)
        else:
            result[x] = {y}
    return pmap(result)
