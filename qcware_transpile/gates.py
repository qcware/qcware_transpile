from pyrsistent import pvector, pset, PSet
from typing import Union, Sequence, Set
import attr

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

    def __str__(self):
        return "".join([self.name, "("]
                  + [",".join([s for s in self.parameter_names])]
                  + ["), ("]
                  + [",".join([str(i) for i in self.qubit_ids])]
                  + [")"])



@attr.s()
class Dialect(object):
    """
    A "dialect" -- essentially just a named set of gate definitions
    """
    name = attr.ib(type=str)
    gate_defs = attr.ib(type=PSet, converter=pset)

    def __str__(self):
        return "\n  ".join([self.name]+[str(g) for g in self.gate_defs])

