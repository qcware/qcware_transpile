from quasar.circuit import Gate
from quasar.circuit import Circuit as QuasarCircuit
from pyrsistent import pset
from pyrsistent.typing import PSet
from typing import Callable
from ..gates import GateDef, Dialect
from ..circuits import Circuit
from inspect import signature


def quasar_gatenames_full() -> PSet[str]:
    """
    The names of verything in the Gate namespace
    """
    return pset(dir(Gate))


def is_builtin(thing) -> bool:
    return type(thing).__name__ in dir(__builtins__) or type(
        thing).__name__ == "builtin_function_or_method"


def function_represents_gate(f) -> bool:
    if (not callable(f)) or is_builtin(f):
        return False
    sig = signature(f)
    has_all_defaults = all([
        param.default is not param.empty for param in sig.parameters.values()
    ])
    if not has_all_defaults:
        return False
    f_result = f()
    if not isinstance(f_result, Gate):
        return False
    return True


def represents_gate(thing) -> bool:
    return function_represents_gate(thing) or isinstance(thing, Gate)


def quasar_gatethings_full() -> PSet:
    """
    All the things in the Gate namespace which represent a gate
    """
    return pset({
        getattr(Gate, name)
        for name in quasar_gatenames_full()
        if represents_gate(getattr(Gate, name))
    })


def gatedef_from_gate(g: Gate) -> GateDef:
    name = g.name
    parameter_names = {k for k in g.parameters.keys()}
    num_qubits = g.nqubit
    return GateDef(name=name,
                   parameter_names=parameter_names,
                   qubit_ids=num_qubits)


def gatedef_from_gatefun(g: Callable) -> GateDef:
    return gatedef_from_gate(g())


def gatedef_from_gatething(thing) -> GateDef:
    if isinstance(thing, Gate):
        return gatedef_from_gate(thing)
    elif callable(thing):
        return gatedef_from_gatefun(thing)
    else:
        assert False


def dialect() -> Dialect:
    """
    Programmatically create the Quasar dialect
    """
    gatedefs = {gatedef_from_gatething(x) for x in quasar_gatethings_full()}
    return Dialect(name="quasar", gate_defs=gatedefs)

def to_circuit(qc: QuasarCircuit):
    instructions = []
    for key, gate in qc.gates.items():
        times, qubits = key
        instructions.append(Instruction(gate_def = gatedef_from_gatething(gate),
                                        bit_bindings = qubits,
                                        parameter_bindings = 
