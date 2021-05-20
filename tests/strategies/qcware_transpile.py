from hypothesis.strategies import (
    composite,
    integers,
    text,
    lists,
    sets,
    just,
    sampled_from,
    one_of,
)
from hypothesis import assume
from qcware_transpile.gates import GateDef, Dialect
from qcware_transpile.instructions import (
    Instruction,
    instruction_parameters_are_fully_bound,
)
from qcware_transpile.circuits import (
    Circuit,
    circuit_bit_targets,
    circuit_parameter_map,
    circuit_is_valid_replacement,
)
from qcware_transpile.matching import (
    TranslationRule,
    TranslationSet,
    circuit_is_simply_translatable_by,
)
from typing import Set, Optional, Tuple, FrozenSet, Callable
import string
import attr

gate_names = text(alphabet=list(string.ascii_lowercase), min_size=4, max_size=7)

parameter_names = text(alphabet=list(string.ascii_lowercase), min_size=3, max_size=5)


@composite
def gate_defs(
    draw,
    names=text(alphabet=list(string.ascii_uppercase), min_size=1, max_size=3),
    num_bits=integers(min_value=1, max_value=3),
    parameter_names=parameter_names,
    min_num_parameters=0,
    max_num_parameters=3,
):
    """
    Create a random gate definition; used to create arbitrary dialects
    """
    return GateDef(
        name=draw(names),
        qubit_ids=draw(num_bits),
        parameter_names=draw(
            sets(
                parameter_names,
                min_size=min_num_parameters,
                max_size=max_num_parameters,
            )
        ),
    )


@composite
def dialects(
    draw,
    min_gates: int = 3,
    max_gates: int = 7,
    name=gate_names,
    max_num_bits=3,
    min_num_parameters=0,
    max_num_parameters=3,
):
    """
    Create a random dialect
    """
    ngates = draw(integers(min_value=min_gates, max_value=max_gates))
    name = draw(name)
    gatedefs = draw(
        lists(
            gate_defs(
                min_num_parameters=min_num_parameters,
                max_num_parameters=max_num_parameters,
                num_bits=integers(min_value=1, max_value=max_num_bits),
            ),
            min_size=ngates,
            max_size=ngates,
            unique_by=lambda x: x.name,
        )
    )
    gatenames = [x.name for x in gatedefs]
    # juuust make sure there are no duplicate gate names
    assert len(gatenames) == len(gatedefs)
    return Dialect(name, set(gatedefs))


@composite
def instructions(
    draw,
    gate_defs: Set,
    qubit_ids: Set[int],
    parameter_values=integers(min_value=0, max_value=100),
):
    """
    Create a random gate definition; requires a fixed list of gate definitions
    (rather than a the gate_defs strategy) so you don't simply get a bunch of
    garbage.
    """
    gates_that_fit = [g for g in gate_defs if len(g.qubit_ids) <= len(qubit_ids)]
    assume(len(gates_that_fit) > 0)
    assert len(gates_that_fit) > 0
    gatedef = draw(sampled_from(gates_that_fit))
    assert len(gatedef.qubit_ids) <= len(qubit_ids)
    parameter_bindings = {
        parameter: draw(parameter_values) for parameter in gatedef.parameter_names
    }
    # ignoring type error below; we are sampling from a set which
    # seems to trigger a mypy error, but seems to work just fine
    bit_bindings = draw(
        lists(
            sampled_from(qubit_ids),  # type: ignore
            min_size=len(gatedef.qubit_ids),
            max_size=len(gatedef.qubit_ids),
            unique=True,
        )
    )
    return Instruction(
        gate_def=gatedef,
        bit_bindings=bit_bindings,
        parameter_bindings=parameter_bindings,
    )


@composite
def qubit_ids(
    draw, min_value: int = 0, max_value: int = 100, min_size: int = 3, max_size: int = 5
):
    return draw(
        lists(
            integers(min_value=min_value, max_value=max_value),
            min_size=min_size,
            max_size=max_size,
            unique=True,
        )
    )


@composite
def circuits(
    draw,
    dialect: Dialect,
    min_length: int = 1,
    max_length: int = 5,
    qubit_ids=qubit_ids(),
    gate_defs: Optional[Set] = None,
    parameter_values=integers(min_value=0, max_value=100),
):
    _qubit_ids = draw(qubit_ids)
    gate_defs = dialect.gate_defs if gate_defs is None else gate_defs  # type: ignore
    _instructions = draw(
        lists(
            instructions(gate_defs, _qubit_ids, parameter_values),
            min_size=min_length,
            max_size=max_length,
        )
    )
    return Circuit.from_instructions(
        dialect_name=dialect.name, instructions=_instructions
    )


@composite
def dialect_and_circuit(
    draw,
    min_gates: int = 3,
    max_gates: int = 7,
    min_circuit_length: int = 3,
    max_circuit_length: int = 5,
    min_num_qubits: int = 3,
    max_num_qubits: int = 5,
    max_qubit_id: int = 100,
    parameter_values=integers(min_value=0, max_value=100),
):
    d = draw(dialects(min_gates=min_gates, max_gates=max_gates))
    min_qubits_required_by_dialect = min([len(g.qubit_ids) for g in d.gate_defs])
    assert min_num_qubits >= min_qubits_required_by_dialect
    c = draw(
        circuits(
            d,
            min_length=min_circuit_length,
            max_length=max_circuit_length,
            qubit_ids=qubit_ids(
                min_value=0,
                max_value=max_qubit_id,
                min_size=min_num_qubits,
                max_size=max_num_qubits,
            ),
            parameter_values=parameter_values,
        )
    )
    return (d, c)


def _mult_by_func(k, v):
    return lambda pm: pm[k] * v


def _add_to_func(k, v):
    return lambda pm: pm[k] + v


@composite
def replacement_parameter_values(
    draw,
    pm_keys: Set[Tuple[int, str]],
    values: FrozenSet[int] = frozenset([1, 2, 3]),
    converters: FrozenSet[Callable] = frozenset([_mult_by_func, _add_to_func]),
):
    """
    Returns either a value sampled from values, a PM key sampled from the given keys
    or a function which adds or multiplies from a given key
    """
    v = draw(sampled_from(list(values)))
    k = draw(sampled_from(list(pm_keys)))
    return draw(
        one_of(
            sampled_from(list(values)),
            sampled_from(list(pm_keys)),
            sampled_from(list(converters)).map(lambda f: f(k, v)),
        )
    )


@composite
def translations(
    draw,
    from_dialect: Dialect,
    to_dialect: Dialect,
    max_translation_from_length=2,
    max_translation_to_length=2,
):
    from_circuit = draw(
        circuits(from_dialect, min_length=1, max_length=max_translation_from_length)
    )
    from_circuit_bits = circuit_bit_targets(from_circuit)
    pm = circuit_parameter_map(from_circuit)
    # we'd like the source circuit to have no parameter bindings
    new_instructions = [
        attr.evolve(i, parameter_bindings={}) for i in from_circuit.instructions
    ]
    from_circuit = attr.evolve(from_circuit, instructions=new_instructions)
    # since we have to have *some* values to pull from,
    # assume there are parameters in the source
    # assume(len(pm.keys()) > 0)
    # assert (len(pm.keys()) > 0)
    to_circuit = draw(
        circuits(
            to_dialect,
            min_length=1,
            max_length=max_translation_to_length,
            qubit_ids=just(list(from_circuit_bits)),
            parameter_values=replacement_parameter_values(pm.keys()),
        )
    )
    to_circuit_bits = circuit_bit_targets(to_circuit)
    assume(from_circuit_bits == to_circuit_bits)
    assert from_circuit_bits == to_circuit_bits
    return TranslationRule(pattern=from_circuit, replacement=to_circuit)


@composite
def translation_sets(
    draw,
    from_dialect: Optional[Dialect] = None,
    to_dialect: Optional[Dialect] = None,
    min_translations: Optional[int] = None,
    max_translations: Optional[int] = None,
    max_translation_from_length=1,
    max_translation_to_length=2,
):
    from_dialect = draw(dialects()) if from_dialect is None else from_dialect
    to_dialect = draw(dialects()) if to_dialect is None else to_dialect
    num_from_gates = len(from_dialect.gate_defs)
    min_translations = (
        num_from_gates
        if min_translations is None
        else min(num_from_gates, min_translations)
    )
    max_translations = (
        num_from_gates
        if max_translations is None
        else min(num_from_gates, max_translations)
    )
    rules = draw(
        lists(
            translations(
                from_dialect,
                to_dialect,
                max_translation_from_length=max_translation_from_length,
                max_translation_to_length=max_translation_to_length,
            ),
            min_size=min_translations,
            max_size=max_translations,
        )
    )
    return TranslationSet(from_dialect=from_dialect, to_dialect=to_dialect, rules=rules)


@composite
def translatable_circuits(draw, ts: TranslationSet):
    one_gate_rules = {r for r in ts.rules if len(r.pattern.instructions) == 1}
    gates = {r.pattern.instructions[0].gate_def for r in one_gate_rules}
    c = draw(circuits(dialect=ts.from_dialect, gate_defs=gates))
    assume(circuit_is_simply_translatable_by(c, ts))
    return c
