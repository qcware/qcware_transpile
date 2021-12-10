from hypothesis import given, note, HealthCheck, settings, assume
from hypothesis.strategies import (
    data,
    lists,
    integers,
    dictionaries,
    tuples,
    sampled_from,
)
from qcware_transpile.gates import Dialect
from qcware_transpile.circuits import (
    Circuit,
    circuit_bit_bindings,
    circuit_bit_binding_signature,
    circuit_pattern_matches_target,
    circuit_bit_targets,
    circuit_parameter_map,
)
from qcware_transpile.instructions import (
    remapped_instruction,
    _is_valid_replacement_parameter_value,
)
from qcware_transpile.helpers import exists_in
from ..strategies import (
    dialect_and_circuit,
    parameter_names,
    replacement_parameter_values,
    dialects,
    translation_sets,
)
from qcware_transpile.matching import trivial_rule
from typing import Tuple
import pytest
import icontract
import attr


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
            c.instructions[binding[0]].bit_bindings[binding[1]] for binding in sig
        }
        assert len(bound_bits) == 1


@given(dialect_and_circuit(min_circuit_length=2, max_circuit_length=4))
@settings(deadline=None, suppress_health_check=[HealthCheck.too_slow])
def test_circuit_pattern_matches_target(dc: Tuple[Dialect, Circuit]):
    d, c = dc
    # first test that the circuit matches itself
    assert circuit_pattern_matches_target(c, c)
    first_instructions_parameters = list(c.instructions[0].parameter_bindings.keys())
    if len(first_instructions_parameters) > 0:
        # change a value of a parameter in the pattern and
        # they should not match
        key = first_instructions_parameters[0]
        val = c.instructions[0].parameter_bindings[key] + 1
        assert val == c.instructions[0].parameter_bindings[key] + 1
        # ok, I love pyrsistent, but changing nested structures can be painful
        p = attr.evolve(
            c,
            instructions=c.instructions.set(
                0,
                attr.evolve(
                    c.instructions[0],
                    parameter_bindings=c.instructions[0].parameter_bindings.set(
                        key, val
                    ),
                ),
            ),
        )

        assert p.instructions[0].parameter_bindings[key] == val
        assert not circuit_pattern_matches_target(p, c)

        # pull a parameter binding out of the pattern and the pattern should
        # still match
        p = attr.evolve(
            c,
            instructions=c.instructions.set(
                0,
                attr.evolve(
                    c.instructions[0],
                    parameter_bindings=c.instructions[0].parameter_bindings.discard(
                        list(c.instructions[0].parameter_bindings.keys())[0]
                    ),
                ),
            ),
        )
        note("***")
        note(str(c))
        note(str(p))
        assert circuit_pattern_matches_target(p, c)

        # we should raise a precondition violation if the target isn't
        # fully bound
        with pytest.raises(icontract.errors.ViolationError):
            assert not circuit_pattern_matches_target(c, p)

    # switch a bit binding in the pattern and it shouldn't match
    if len(c.instructions) > 1:
        bbs = circuit_bit_binding_signature(c)
        # we have to find a case where two bits are bound to the same thing
        candidates = [x for x in bbs if len(x) > 1]
        if len(candidates) > 0:
            bit_to_change = list(candidates[0])[0]
            instruction = c.instructions[bit_to_change[0]]
            bit_bindings = instruction.bit_bindings
            new_bindings = bit_bindings.set(bit_to_change[1], 1024)
            new_instruction = attr.evolve(instruction, bit_bindings=new_bindings)
            p = attr.evolve(
                c, instructions=c.instructions.set(bit_to_change[0], new_instruction)
            )
            assert circuit_bit_binding_signature(p) != circuit_bit_binding_signature(c)
            assert not circuit_pattern_matches_target(p, c)


@given(replacement_parameter_values([(1, "bob"), (2, "tim")]))
def test_replacement_parameter_values(v):
    assert _is_valid_replacement_parameter_value(v)


@given(data())
def test_remap_instruction(data):
    parameter_map = data.draw(
        dictionaries(
            keys=tuples(integers(), parameter_names),
            values=integers(),
            min_size=3,
            max_size=3,
        )
    )
    d, c = data.draw(
        dialect_and_circuit(
            min_gates=3,
            max_gates=3,
            min_circuit_length=1,
            max_circuit_length=1,
            parameter_values=sampled_from(list(parameter_map.keys())),
        )
    )
    # let's make a random mapping from the circuit bits to arbitratry integers
    bits = list(circuit_bit_targets(c))
    new_bits = data.draw(lists(integers(), min_size=len(bits), max_size=len(bits)))
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
    assert set(rmi.parameter_bindings.values()).issubset(set(parameter_map.values()))


# the data generation for this is tricky and the strategies need to be revisited
# because it takes far too long to create two dialects with a translation table
# and generatable circuits which can be translated
@given(data())
@settings(suppress_health_check=[HealthCheck.too_slow, HealthCheck.filter_too_much])
def test_translate_circuit(data):
    d1 = data.draw(
        dialects(
            min_gates=5, min_num_parameters=0, max_num_parameters=0, max_num_bits=1
        )
    )
    note("From dialect")
    note(str(d1))
    d2 = data.draw(
        dialects(
            min_gates=5, min_num_parameters=0, max_num_parameters=0, max_num_bits=1
        )
    )
    note("To dialect")
    note(str(d2))
    ts = data.draw(translation_sets(d1, d2, min_translations=3))
    # note("Translation table")
    # note(str(ts))
    ## from_circuit = data.draw(translatable_circuits(ts))
    # note("from_circuit")
    # note(str(from_circuit))
    # to_circuit = simple_translate(ts, from_circuit)
    # note("to_circuit")
    # note(str(to_circuit))
    # note("to_circuit gates")
    # note({i.gate_def for i in to_circuit.instructions})
    # note("to_dialect gates")
    # note(d2.gate_defs)
    # assert circuit_conforms_to_dialect(to_circuit, d2)


@given(
    data=data(),
    num_parameters=integers(min_value=0, max_value=1),
    num_bits=integers(min_value=1, max_value=3),
)
@settings(suppress_health_check=[HealthCheck.too_slow])
def test_trivial_rule(data, num_parameters, num_bits):
    """
    This is honestly a bit more of a smoke test than anything else; it
    exercises the pre- and post-conditions for testing
    """
    dialect_a = data.draw(
        dialects(
            min_gates=7,
            min_num_parameters=num_parameters,
            max_num_parameters=num_parameters,
            max_num_bits=num_bits,
        )
    )
    dialect_b = data.draw(
        dialects(
            min_gates=7,
            min_num_parameters=num_parameters,
            max_num_parameters=num_parameters,
            max_num_bits=num_bits,
        )
    )

    def simple_pred(x):
        """
        We want to make sure that in both dialect A and B,
        there exists at least one gate with the desired number
        of parameters and which uses the max number of bits.  Trivial
        Rules handle up to one parameter.
        """
        return len(x.parameter_names) == num_parameters and len(x.qubit_ids) == num_bits

    assume(exists_in(dialect_a.gate_defs, simple_pred))
    assume(exists_in(dialect_b.gate_defs, simple_pred))
    gate_def_a = list(filter(simple_pred, dialect_a.gate_defs))[0]
    gate_def_b = list(filter(simple_pred, dialect_b.gate_defs))[0]
    rule = trivial_rule(dialect_a, gate_def_a, dialect_b, gate_def_b)
