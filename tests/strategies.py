from hypothesis.strategies import (composite, integers, text, lists, sets,
                                   sampled_from)
from hypothesis import assume
from qcware_transpile.matching import GateDef, instruction, dialect, circuit
from typing import Set, Mapping
import string


@composite
def gate_defs(draw,
              names=text(alphabet=list(string.ascii_uppercase),
                         min_size=1,
                         max_size=3),
              num_bits=integers(min_value=1, max_value=3),
              parameter_names=text(alphabet=list(string.ascii_lowercase),
                                   min_size=3,
                                   max_size=5)):
    """
    Create a random gate definition; used to create arbitrary dialects
    """
    return GateDef(name=draw(names),
                   qubit_ids=draw(num_bits),
                   parameter_names=draw(
                       sets(parameter_names, min_size=1, max_size=3)))


@composite
def dialects(draw,
             min_gates: int = 3,
             max_gates: int = 7,
             name=text(alphabet=list(string.ascii_lowercase),
                       min_size=4,
                       max_size=7)):
    """
    Create a random dialect
    """
    ngates = draw(integers(min_value=min_gates, max_value=max_gates))
    name = draw(name)
    gatedefs = draw(lists(gate_defs(), min_size=ngates, max_size=ngates))
    gatenames = [x.name for x in gatedefs]
    assume(len(set(gatenames)) == len(gatenames))
    return dialect(name, gatedefs)


@composite
def instructions(draw,
                 gate_defs: Set,
                 qubit_ids: Set[int],
                 min_parameter=0,
                 max_parameter=100):
    """
    Create a random gate definition; requires a fixed list of gate definitions
    (rather than a the gate_defs strategy) so you don't simply get a bunch of
    garbage.
    """
    gatedef = draw(
        sampled_from(
            [g for g in gate_defs if len(g.qubit_ids) <= len(qubit_ids)]))
    assume(len(gatedef.qubit_ids) <= len(qubit_ids))
    parameter_bindings = {
        parameter:
        draw(integers(min_value=min_parameter, max_value=max_parameter))
        for parameter in gatedef.parameter_names
    }
    bit_bindings = draw(
        lists(sampled_from(qubit_ids),
              min_size=len(gatedef.qubit_ids),
              max_size=len(gatedef.qubit_ids),
              unique=True))
    return instruction(gatedef, bit_bindings, parameter_bindings)


@composite
def circuits(draw,
             dialect: Mapping,
             min_length=1,
             max_length=5,
             min_num_qubits=1,
             max_num_qubits=5,
             min_parameter=0,
             max_parameter=100):
    qubit_ids = draw(
        lists(integers(min_value=0, max_value=max_num_qubits - min_num_qubits),
              min_size=min_num_qubits,
              max_size=max_num_qubits,
              unique=True))
    _instructions = draw(
        lists(instructions(dialect['gate_defs'], qubit_ids, min_parameter,
                           max_parameter),
              min_size=min_length,
              max_size=max_length))
    return circuit(dialect.name, _instructions)


@composite
def dialect_and_circuit(draw,
                        min_gates: int = 3,
                        max_gates: int = 7,
                        min_circuit_length: int = 3,
                        max_circuit_length: int = 5,
                        min_num_qubits: int = 3,
                        max_num_qubits: int = 5,
                        min_parameter: int = 0,
                        max_parameter: int = 100):
    d = draw(dialects(min_gates=min_gates, max_gates=max_gates))
    min_qubits_required_by_dialect = min(
        [len(g.qubit_ids) for g in d['gate_defs']])
    assert min_num_qubits >= min_qubits_required_by_dialect
    c = draw(
        circuits(d,
                 min_length=min_circuit_length,
                 max_length=max_circuit_length,
                 min_num_qubits=min_num_qubits,
                 max_num_qubits=max_num_qubits,
                 min_parameter=min_parameter,
                 max_parameter=max_parameter))
    return (d, c)