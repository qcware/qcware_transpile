import pyzx  # type: ignore
from qcware_transpile.gates import GateDef, Dialect
from qcware_transpile.circuits import Circuit
from qcware_transpile.instructions import Instruction
from qcware_transpile.helpers import map_seq_to_seq_unique
from pyrsistent import pset
from pyrsistent.typing import PSet, PMap
from typing import Tuple, Any, Set, Sequence
from inspect import isclass, signature
import numpy as np  # type: ignore

__dialect_name__ = "qiskit"


def pyzx_gatethings() -> PSet[Any]:
    """
    The set of all things in qiskit which represent a gate
    """
    possible_things = [
        x for x in pyzx.circuit.gates.__dict__.values() if isclass(x)
        and issubclass(x, pyzx.circuit.Gate) and x != pyzx.circuit.Gate
    ]
    return possible_things


def parameter_names_from_gatething(thing: pyzx.circuit.Gate) -> PSet[str]:
    sig = signature(thing.__init__)
    result = set(sig.parameters.keys()).difference(
        {'self', 'target', 'control', 'ctrl1', 'ctrl2', 'label'})
    return pset(result)


def number_of_qubits_from_gatething(thing: pyzx.circuit.Gate) -> int:
    # unfortunately it's not obvious from just the class how many qubits
    # the gate can operate on, and pretty much the only path forward
    # seems to be to instantiate the gate and see.  That means coming
    # up with fake parameter arguments.
    param_names = list(signature(thing.__init__).parameters.keys())
    # in pyzx rather than having a vector of target bits, you have bit names,
    # such as "ctrl1", "ctrl2", "target"
    result = 0
    if "target" in param_names:
        result = result + 1
    if "control" in param_names:
        result = result + 1
    else:
        if "ctrl1" in param_names:
            result = result + 1
        if "ctrl2" in param_names:
            result = result + 1
    return result


def gatedef_from_gatething(thing) -> GateDef:
    return GateDef(
        name=thing.__name__,
        parameter_names=parameter_names_from_gatething(thing),  # type: ignore
        qubit_ids=number_of_qubits_from_gatething(thing))


# some gates are problematic -- in particular Qiskit's "gates" which
# really just generate other gates, for example those which take a
# number of bits as an argument.  for now we are disabling those
Problematic_gatenames = pset({})


def attempt_gatedefs() -> Tuple[PSet[GateDef], PSet[str]]:
    """
    Iterate through all the gate definitions and build a set of successful
    gate definitions and a list of things which could not be converted
    """
    all_things = pyzx_gatethings()
    success = set()
    failure = set()
    for thing in all_things:
        try:
            gd = gatedef_from_gatething(thing)
            if gd.name in Problematic_gatenames:
                failure.add(thing.__name__)
            else:
                success.add(gd)
        except Exception:
            failure.add(thing.__name__)
    return (pset(success), pset(failure))


def gate_defs() -> PSet[GateDef]:
    s, f = attempt_gatedefs()
    return s


def gate_names() -> PSet[str]:
    return pset([g.name for g in gate_defs()])


def dialect() -> Dialect:
    """
    The pyzx dialect
    """
    return Dialect(name=__dialect_name__,
                   gate_defs=gate_defs())  # type: ignore


def parameter_bindings_from_gate(gate: qiskit.circuit.Gate) -> PMap[str, Any]:
    # this is a little trickier than others.  Rather than storing parameters
    # in a dictionary, pyzx stores them as individual Gate members, ie
    # self.target, self.phi, etc.
    not_parameters = {'label'}
    values = gate.params
    names = [k for k, v in signature(gate.__init__).parameters.items()
             ][0:len(values)]
    return map_seq_to_seq_unique(names, values)


def qubit_bindings(g: pyzx.circuit.Gate):
    """
    Gets an ordered set of qubit bindings for the given gate.
    Pyzx, rather sensibly, does gates with names bound to qubits,
    whereas we usually store an ordered list of qubits.  For pyzx,
    then,
    1 qubit -> target
    2 qubit -> control, target
    3 qubit -> ctrl1, ctrl2, target
    """
    if "ctrl1" in dir(g):
        result = [g.ctrl1, g.ctrl2, g.target]
    elif "control" in dir(g):
        result = [g.control, g.target]
    else:
        result = [g.target]
    return result


def native_to_circuit(pc: pyzx.circuit.Circuit) -> Circuit:
    """
    Return a transpile-style Circuit object from a qiskit Circuit object
    """
    instructions = []
    d = dialect()
    valid_names = [g.name for g in d.gate_defs]
    for g in pc.gates:
        gate_name = g.__class__.__name__
        assert (gate_name in valid_names)
        gate_def = gatedef_from_gatething(g.__class__)
        parameter_bindings = parameter_bindings_from_gate(g)
        bindings = qubit_bindings(g)
        instructions.append(
            Instruction(
                gate_def=gate_def,
                parameter_bindings=parameter_bindings,  # type: ignore
                bit_bindings=bindings))
    qubits = list(range(pc.qubits))
    return Circuit(
        dialect_name=__dialect_name__,
        instructions=instructions,  # type: ignore
        qubits=qubits)

def pyzx_qubit_bindings(qubits: Sequence[int]):
    if len(qubits) == 3:
        result = {'ctrl1': qubits[0],
                  'ctrl2': qubits[1],
                  'target': qubits[2] }
    elif len(qubits) == 2:
        result = {'control': qubits[0],
                  'target' : qubits[1] }
    elif len(qubits) == 1:
        result = {'target': qubits[1]}
    else:
        assert False
    return result


def pyzx_gate_from_instruction(i: Instruction):
    """
    Create a qiskit Gate object from an instruction
    """
    gclass = getattr(pyzx.circuit.gates, i.gate_def.name)
    parms = i.parameter_bindings
    parms = parms.update(pyzx_qubit_bindings(i.bit_bindings))
    gate = gclass(**i.parameter_bindings)
    return gate


def circuit_to_native(c: Circuit) -> pyzx.Circuit:
    """
    Make a qiskit circuit from a qcware_transpile Circuit
    """
    # qiskit wants the number of qubits first.
    num_qubits = max(c.qubits) - min(c.qubits) + 1
    qr = qiskit.QuantumRegister(num_qubits)
    result = qiskit.QuantumCircuit(qr)
    for instruction in c.instructions:
        g = qiskit_gate_from_instruction(instruction)
        result.append(g, instruction.bit_bindings)
    result = result.reverse_bits()
    return result


def native_circuits_are_equivalent(c1: qiskit.QuantumCircuit,
                                   c2: qiskit.QuantumCircuit) -> bool:
    """
    Whether or not two circuits are equivalent.  Not having a test_equivalence
    method here, we brute-force it by evaluating statevectors
    """
    backend = qiskit.Aer.get_backend('statevector_simulator')
    sv1 = qiskit.execute(c1, backend).result().data()['statevector']
    sv2 = qiskit.execute(c2, backend).result().data()['statevector']
    return np.isclose(sv1, sv2).all()
