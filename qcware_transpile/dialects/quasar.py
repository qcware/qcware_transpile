"""
Functions and structures involved with extracting a usable
Dialect from quasar, and converting to and from Quasar
Circuits (and possibly returns)
"""
from quasar.circuit import Gate  # type: ignore
from quasar.circuit import Circuit as QuasarCircuit  # type: ignore
from pyrsistent import pset
from pyrsistent.typing import PSet
from typing import Callable, Any
# not using relative imports here for the moment to simplify emacs
# send-to-buffer issues; it should arguably be set back to relative
# imports at some point
from qcware_transpile.gates import GateDef, Dialect
from qcware_transpile.circuits import Circuit
from qcware_transpile.instructions import Instruction
from qcware_transpile.helpers import map_seq_to_seq_unique
from inspect import signature
from dpcontracts import require # type: ignore

__dialect_name__ = "quasar"


def is_builtin(thing) -> bool:
    """
    Whether or not something is a Python builtin; used to filter
    out things in the Gate namespace which represent a Gate or the
    function used to create a gate.
    """
    return type(thing).__name__ in dir(__builtins__) or type(
        thing).__name__ == "builtin_function_or_method"


def represents_gate(f) -> bool:
    """
    As expected: whether or not a thing represents a gate
    (either by being a Gate or by being a callable with
    fully-populated defaults which returns a Gate object)
    """
    if isinstance(f, Gate):
        return True
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


def gatedef_from_gate(name: str, g: Gate) -> GateDef:
    """
    Create a gatedef from a gate object.  We use a given
    name instead of g.name because gate "names" in quasar
    don't always correspond to the Python names (for example,
    Gate.ST has name = 'S^+', but for our dialect we want
    the mapping to Python to be as simple as possible)
    """
    name = name
    parameter_names = {k for k in g.parameters.keys()}
    num_qubits = g.nqubit
    return GateDef(name=name,
                   parameter_names=parameter_names,
                   qubit_ids=num_qubits)


def gatedef_from_gatefun(name: str, g: Callable) -> GateDef:
    """
    Creates a gatedef from a function that returns a gate;
    see above for reasons we have an explicit name
    """
    return gatedef_from_gate(name, g())

@require("thing must represent a gate",
         lambda args: represents_gate(args.thing))
def gatedef_from_gatething(name: str, thing: Any) -> GateDef:
    if isinstance(thing, Gate):
        return gatedef_from_gate(name, thing)
    elif callable(thing):
        return gatedef_from_gatefun(name, thing)
    else:
        assert False


@require("thing must represent a gate",
         lambda args: represents_gate(args.thing))
def gate_name_property(thing: Any) -> str:
    """
    Return the .name property of a Gate (or Gate
    returned by a callable function)
    """
    if isinstance(thing, Gate):
        return thing.name
    elif callable(thing):
        g = thing()
        assert (isinstance(g, Gate))
        return g.name
    else:
        assert False
        return None


def quasar_gatenames_full() -> PSet[str]:
    """
    The names of verything in the Gate namespace
    """
    return pset(
        {name
         for name in dir(Gate) if represents_gate(getattr(Gate, name))})


def quasar_gatethings_full() -> PSet:
    """
    All the things in the Gate namespace which represent a gate
    """
    return pset({
        getattr(Gate, name)
        for name in quasar_gatenames_full()
        if represents_gate(getattr(Gate, name))
    })


def dialect() -> Dialect:
    """
    Programmatically create the Quasar dialect
    """
    gatedefs = {
        gatedef_from_gatething(name, getattr(Gate, name))
        for name in quasar_gatenames_full()
    }
    return Dialect(name="quasar", gate_defs=gatedefs)  # type: ignore


def name_property_to_namespace_translation_table():
    """
    Okay... names in the Gate namespace for gates ("ST") don't always translate
    to the gate's .name property (in the ST case, "S^+").  So this is a translation
    table from the gate's name property to the name in the Gate namespace
    """
    namespace_names = list(quasar_gatenames_full())
    name_property = [
        gate_name_property(getattr(Gate, name)) for name in namespace_names
    ]
    return map_seq_to_seq_unique(name_property, namespace_names)


def native_to_circuit(qc: QuasarCircuit) -> Circuit:
    """
    Return a transpile-style Circuit object from a quasar Circuit object
    """
    instructions = []
    ntt = name_property_to_namespace_translation_table()
    for key, gate in qc.gates.items():
        times, qubits = key
        instructions.append(
            Instruction(gate_def=gatedef_from_gatething(ntt[gate.name], gate),
                        bit_bindings=qubits,
                        parameter_bindings=gate.parameters))
    return Circuit(dialect_name=__dialect_name__, instructions=instructions) # type: ignore


def quasar_gate_from_instruction(i: Instruction)->Gate:
    """
    Create a quasar Gate object from an instruction
    """
    g = getattr(Gate, i.gate_def.name)
    # if g is a Gate, it shouldn't have parameters; if it's a callable,
    # it should.
    if len(i.parameter_bindings.keys()) > 0 :
        g = g(**i.parameter_bindings)
    return g


def circuit_to_native(c: Circuit) -> QuasarCircuit:
    result = QuasarCircuit()
    for instruction in c.instructions:
        g = quasar_gate_from_instruction(instruction)
        result.add_gate(g, tuple(instruction.bit_bindings))
    return result
