from pyrsistent import pvector, pset
from pyrsistent.typing import PSet
from dpcontracts import require  # type: ignore
from qcware_transpile.helpers import exists_in
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
        return "".join([self.name, "("] +
                       [",".join([s
                                  for s in self.parameter_names])] + ["), ("] +
                       [",".join([str(i) for i in self.qubit_ids])] + [")"])


@attr.s()
class Dialect(object):
    """
    A "dialect" -- essentially just a named set of gate definitions
    """
    name = attr.ib(type=str)
    gate_defs = attr.ib(type=PSet[GateDef], converter=pset)

    def __str__(self):
        return "\n  ".join([self.name] + [str(g) for g in self.gate_defs])

    def has_gate_named(self, name: str) -> bool:
        return exists_in(self. gate_defs, lambda x: x.name == name)

    @require("Dialect must have gate to return it",
             lambda args: args.self.has_gate_named(args.name))
    def gate_named(self, name: str) -> GateDef:
        return [x for x in self.gate_defs if x.name == name][0]
