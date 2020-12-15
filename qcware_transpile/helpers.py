"""
Some helper functions
"""
from typing import Sequence, Mapping
from dpcontracts import require  # type: ignore
from pyrsistent import pmap, pset
from typing import TypeVar, Dict
from pyrsistent.typing import PMap, PSet

A = TypeVar('A')
B = TypeVar('B')


@require("Sequences must be the same length",
         lambda args: len(args.s1) == len(args.s2))
def map_seq_to_seq(s1: Sequence[A], s2: Sequence[B]) -> PMap[A, PSet[B]]:
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
    result: dict = {}
    for i in range(len(s1)):
        x = s1[i]
        y = s2[i]
        if x in result:
            result[x] = result[x].add(y)
        else:
            result[x] = pset([y])
    # we now have a mapping of Any to Set[Any], but since
    # we'll be reversing this later, we must map all values to PSet[Any]
    return pmap(result)


@require("Sequences must be the same length",
         lambda args: len(args.s1) == len(args.s2))
@require("Mapping must be unique (len(range)==len(domain))", lambda args: len(
    set(zip(args.s1, args.s2))) == len(set(args.s1)) == len(set(args.s2)))
def map_seq_to_seq_unique(s1: Sequence[A], s2: Sequence[B]) -> PMap[A, B]:
    """
    Much like map_seq_to_seq, in this case provide a direct
    mapping between the sequences (s1 and S2 must have unique values and
    no mapping from s1 to s2 should be multiply defined)
    """
    result = pmap({k: v for (k, v) in zip(s1, s2)})
    return result


def prepend_index_to_domain(index: int, f: Mapping):
    """
    Transforms the keys of a mapping into a tuple with
    the index as the first element; in other words,
    if f = { 1: 2, 3: 4 }, prepend_index_to_domain(3,f)
    would return { (3,1): 2, (3,3): 4 }
    """
    return pmap({(index, k): v for k, v in f.items()})


def reverse_map(f: Mapping[A, B]) -> PMap[B, PSet[A]]:
    """
    Reverses a mapping such that the values of f
    are mapped to the sets of keys in f corresponding 
    to that value
    """
    result: Dict[B, PSet[A]] = {}
    for k, v in f.items():
        if v in result:
            result[v] = result[v].add(k)
        else:
            result[v] = pset([k])
    return pmap(result)
