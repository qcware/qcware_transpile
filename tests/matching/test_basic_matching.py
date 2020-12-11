from hypothesis import given, note
from hypothesis.strategies import (data, lists, integers, dictionaries, tuples,
                                   sampled_from)
from qcware_transpile.gates import Dialect
from qcware_transpile.circuits import (Circuit, circuit_bit_bindings,
                                       circuit_bit_binding_signature,
                                       circuit_pattern_matches_target,
                                       circuit_bit_targets,
                                       circuit_parameter_map)
from qcware_transpile.instructions import (remapped_instruction)
from ..strategies import dialect_and_circuit, parameter_names
from typing import Tuple
import copy
import pytest
import dpcontracts  # type: ignore


@given(dialect_and_circuit())
def test_circuit_parameter_map(dc: Tuple[Dialect, Circuit]):
    d, c = dc
    pm = circuit_parameter_map(c)
    for k, v in pm.items():
        assert c.instructions[k[0]].parameter_bindings[k[1]] == v


@given(dialect_and_circuit())
def test_circuit_bit_bindings(dc: Tuple[Dialect, Circuit]):
    d, c = dc
    bb = circuit_bit_bindings(c)
    for k, v in bb.items():
        instruction_index = k[0]
        bit_index = k[1]
        assert c.instructions[instruction_index].bit_bindings[bit_index] in v


@given(dialect_and_circuit())
def test_bit_binding_signature(dc: Tuple[Dialect, Circuit]):
    d, c = dc
    bbs = circuit_bit_binding_signature(c)
    for sig in bbs:
        # a signature is the set of tuples representing
        # bit IDs in the circuit which are bound to the same
        # bit target
        bound_bits = {
            c.instructions[binding[0]].bit_bindings[binding[1]]
            for binding in sig
        }
        assert len(bound_bits) == 1


@given(dialect_and_circuit(min_circuit_length=2, max_circuit_length=4))
def test_circuit_pattern_matches_target(dc: Tuple[Dialect, Circuit]):
    d, c = dc
    # first test that the circuit matches itself
    assert circuit_pattern_matches_target(c, c)
    first_instructions_parameters = list(
        c.instructions[0].parameter_bindings.keys())
    if len(first_instructions_parameters) > 0:
        # change a value of a parameter in the pattern and
        # they should not match
        p = copy.deepcopy(c)
        key = first_instructions_parameters[0]
        val = p.instructions[0].parameter_bindings[key] + 1
        assert val == p.instructions[0].parameter_bindings[key] + 1
        p.instructions[0].parameter_bindings = p.instructions[
            0].parameter_bindings.set(key, val)  # type: ignore
        assert p.instructions[0].parameter_bindings[key] == val
        assert not circuit_pattern_matches_target(p, c)

        # pull a parameter binding out of the pattern and the pattern should
        # still match
        p = copy.deepcopy(c)
        p.instructions[0].parameter_bindings = p.instructions[  # type: ignore
            0].parameter_bindings.discard(
                list(p.instructions[0].parameter_bindings.keys())[0])
        assert circuit_pattern_matches_target(p, c)

    # we should raise a precondition violation if the target isn't
    # fully bound
    note("***")
    note(str(c))
    note(str(p))
    with pytest.raises(dpcontracts.PreconditionError):
        assert not circuit_pattern_matches_target(c, p)

    # switch a bit binding in the pattern and it shouldn't match
    if len(c.instructions) > 1:
        p = copy.deepcopy(c)
        bbs = circuit_bit_binding_signature(p)
        # we have to find a case where two bits are bound to the same thing
        candidates = [x for x in bbs if len(x) > 1]
        if len(candidates) > 0:
            bit_to_change = list(candidates[0])[0]
            p.instructions[bit_to_change[0]].bit_bindings = p.instructions[
                bit_to_change[0]].bit_bindings.set(bit_to_change[1], 1024)
            assert circuit_bit_binding_signature(
                p) != circuit_bit_binding_signature(c)
            assert not circuit_pattern_matches_target(p, c)


@given(data())
def test_remap_instruction(data):
    parameter_map = data.draw(
        dictionaries(keys=tuples(integers(), parameter_names),
                     values=integers(),
                     min_size=3,
                     max_size=3))
    d, c = data.draw(
        dialect_and_circuit(min_gates=3,
                            max_gates=3,
                            min_circuit_length=1,
                            max_circuit_length=1,
                            parameter_values=sampled_from(
                                list(parameter_map.keys()))))
    # let's make a random mapping from the circuit bits to arbitratry integers
    bits = list(circuit_bit_targets(c))
    new_bits = data.draw(
        lists(integers(), min_size=len(bits), max_size=len(bits)))
    note(str(c))
    note(f"{bits}->{new_bits}")
    qubit_map = {bits[i]: new_bits[i] for i in range(len(bits))}
    i = c.instructions[0]
    rmi = remapped_instruction(qubit_map, parameter_map, i)
    note(str(rmi))
    # the bits of the new instruction should be the same as the set of new bits
    assert set(rmi.bit_bindings) == set(new_bits)
    # the values of the parameters in the new instruction should be in the set
    # of values of the parameter map
    assert set(rmi.parameter_bindings.values()).issubset(
        set(parameter_map.values()))
