import qiskit  # type: ignore
from qcware_transpile.gates import GateDef, Dialect
from qcware_transpile.circuits import Circuit
from qcware_transpile.instructions import Instruction
from qcware_transpile.helpers import map_seq_to_seq_unique
from pyrsistent import pset
from pyrsistent.typing import PSet, PMap
from typing import Tuple, Any, Set
from inspect import isclass, signature
import numpy as np  # type: ignore

__dialect_name__ = "qiskit"


def qiskit_gatethings() -> PSet[Any]:
    """
    The set of all things in qiskit which represent a gate
    """
    possible_things = qiskit.circuit.library.__dict__.values()
    return pset({
        x
        for x in possible_things
        if isclass(x) and issubclass(x, qiskit.circuit.Gate)
    })


def parameter_names_from_gatething(thing: qiskit.circuit.Gate) -> PSet[str]:
    sig = signature(thing.__init__)
    result = set(sig.parameters.keys()).difference(
        {'self', 'label', 'ctrl_state'})
    return pset(result)


def number_of_qubits_from_gatething(thing: qiskit.circuit.Gate) -> int:
    # unfortunately it's not obvious from just the class how many qubits
    # the gate can operate on, and pretty much the only path forward
    # seems to be to instantiate the gate and see.  That means coming
    # up with fake parameter arguments.
    param_names = parameter_names_from_gatething(thing)
    # Obviously not every parameter can be a float, but let's start
    # there.  setting everything to zero also takes care of the
    # ctrl_state parameter which doesn't matter so much for basic gate
    # instantiation, but could affect specialized applications
    # also note that the standard for qiskit is that the first X bits of
    # a controlled gate are the control bits
    # ("In the new gate the first ``num_ctrl_qubits``
    # of the gate are the controls."), see
    # https://github.com/Qiskit/qiskit-terra/qiskit/circuit/controlledgate.py
    params = {k: 0 for k in param_names}
    g = thing(**params)
    return g.num_qubits


def gatedef_from_gatething(thing) -> GateDef:
    return GateDef(
        name=thing.__name__,
        parameter_names=parameter_names_from_gatething(thing),  # type: ignore
        qubit_ids=number_of_qubits_from_gatething(thing))


# some gates are problematic -- in particular Qiskit's "gates" which
# really just generate other gates, for example those which take a
# number of bits as an argument.  for now we are disabling those
Problematic_gatenames = pset({"MSGate"})


def attempt_gatedefs() -> Tuple[PSet[GateDef], PSet[str]]:
    """
    Iterate through all the gate definitions and build a set of successful
    gate definitions and a list of things which could not be converted
    """
    all_things = qiskit_gatethings()
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
    The qiskit dialect
    """
    return Dialect(name=__name__, gate_defs=gate_defs())  # type: ignore


def parameter_bindings_from_gate(gate: qiskit.circuit.Gate) -> PMap[str, Any]:
    values = gate.params
    names = [k for k, v in signature(gate.__init__).parameters.items()
             ][0:len(values)]
    return map_seq_to_seq_unique(names, values)


def native_to_circuit(qc: qiskit.QuantumCircuit) -> Circuit:
    """
    Return a transpile-style Circuit object from a qiskit Circuit object
    """
    instructions = []
    d = dialect()
    valid_names = [g.name for g in d.gate_defs]
    qc = qc.reverse_bits()
    for (instruction, qubits, cbits) in qc.data:
        assert (len(cbits) == 0)
        gate_name = instruction.__class__.__name__
        assert (gate_name in valid_names)
        gate_def = gatedef_from_gatething(instruction.__class__)
        parameter_bindings = parameter_bindings_from_gate(instruction)
        qubit_bindings = [qb.index for qb in qubits]
        instructions.append(
            Instruction(
                gate_def=gate_def,
                parameter_bindings=parameter_bindings,  # type: ignore
                bit_bindings=qubit_bindings))
    qubits = list(range(qc.num_qubits))
    return Circuit(dialect_name=__dialect_name__,
                   instructions=instructions,   # type: ignore
                   qubits=qubits)


def qiskit_gate_from_instruction(i: Instruction):
    """
    Create a qiskit Gate object from an instruction
    """
    gclass = getattr(qiskit.circuit.library, i.gate_def.name)
    gate = gclass(**i.parameter_bindings)
    return gate


def circuit_to_native(c: Circuit) -> qiskit.QuantumCircuit:
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
