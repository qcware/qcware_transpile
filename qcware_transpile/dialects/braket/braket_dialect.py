from braket.circuits import gates, Gate
from qcware_transpile.gates import GateDef, Dialect
from pyrsistent import pset
from pyrsistent.typing import PSet
from typing import Tuple, Any
from inspect import isclass, signature

__dialect_name__ = "braket"

# don't include the AngledGate and Gate base classes in
# the set of all things in braket which represent a gate.
_do_not_include_instructions = pset({'AngledGate', 'Gate'})

def braket_gatethings() -> PSet[Any]:
    """
    The set of all things in braket which represent a gate.
    """
    possible_things = dir(gates)
    return pset([
        getattr(gates, x) 
        for x in possible_things 
        if isclass(getattr(gates, x)) and issubclass(getattr(gates, x), Gate) and x not in _do_not_include_instructions
    ])

def parameter_names_from_gatething(thing: Gate) -> PSet[str]:
    sig = signature(thing.__init__)
    result = set(sig.parameters.keys()).difference({'self', 'display_name'})
    return pset(result)

def number_of_qubits_from_gatething(thing: Gate) -> int:
    # unfortunately it's not obvious from just the class how many qubits
    # the gate can operate on, and pretty much the only path forward
    # seems to be to instantiate the gate and see.  That means coming
    # up with fake parameter arguments. Some gate initialization methods
    # accept an angle parameter, which we set to zero. 
    param_names = parameter_names_from_gatething(thing)
    params = {k: 0 for k in param_names}
    g = thing(**params)
    return g.qubit_count

def gatedef_from_gatething(thing: Gate) -> GateDef:
    return GateDef(
        name=thing.__name__,
        parameter_names = parameter_names_from_gatething(thing),
        qubit_ids = number_of_qubits_from_gatething(thing))

# the Unitary gate is problematic since it allows for
# the construction of a gate with an arbitrary matrix.
# for now we will disable the Unitary gate.
Problematic_gatenames = pset({'Unitary'})

def attempt_gatedefs() -> Tuple[PSet[GateDef], PSet[str], PSet[type]]:
    """
    Iterate through all the gate definitions and build a set of successful
    gate definitions and a list of things which could not be converted
    """
    all_things = braket_gatethings()
    success = set()
    successful_things = set()
    failure = set()
    for thing in all_things:
        try:
            gd = gatedef_from_gatething(thing)
            if gd.name in Problematic_gatenames:
                failure.add(thing.__name__)
            else:
                success.add(gd)
                successful_things.add(thing)
        except Exception:
            failure.add(thing.__name__)
    return (pset(success), pset(failure), pset(successful_things))

def gate_defs() -> PSet[GateDef]:
    return attempt_gatedefs()[0]

def dialect() -> Dialect:
    """
    The braket dialect
    """
    return Dialect(name=__dialect_name__,
                   gate_defs=gate_defs())