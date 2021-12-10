"""Classes, functions, and data structures to create "Builders" for circuits.
"""

from functools import partial
from typing import Any, Callable

from qcware_transpile.circuits import Circuit
from qcware_transpile.gates import Dialect
from qcware_transpile.instructions import Instruction


class Builder:
    def __init__(self, dialect: Dialect):
        self.dialect = dialect
        self.instructions: list[Instruction] = []

    def add_instruction(
        self, gate_name: str, bits: list, parameters: dict, metadata: dict
    ) -> "Builder":
        self.instructions.append(
            Instruction(
                gate_def=self.dialect.gate_named(gate_name),
                bit_bindings=bits,
                parameter_bindings=parameters,
                metadata=metadata,
            )
        )
        return self


def create_builder(dialect: Dialect, to_native_func: Callable[[Circuit], Any]):
    """
    Creates a builder object, starting from a basically empty class and
    adding functions to "build" a circuit from scratch based on the gates
    in the dialect and the parameters involved.
    """
    result = Builder(dialect)

    def create_method(gate_def):
        def add_this_gate(self: Builder, *args, **kwargs):
            gate_name = gate_def.name
            bits = list(args)
            parameters: dict = kwargs
            metadata: dict = dict()
            self.add_instruction(gate_name, bits, parameters, metadata)
            return self

        return add_this_gate

    for gate_def in dialect.gate_defs:

        # now bind this method to the object instance.  It may be better to create
        # a class dynamically and then create members of that class; let's try this
        # first.
        # see https://newbedev.com/adding-a-method-to-an-existing-object-instance
        # for descriptions
        setattr(result, gate_def.name, partial(create_method(gate_def), result))

    setattr(
        result,
        "circuit",
        partial(
            lambda self: Circuit.from_instructions(
                self.dialect.name, self.instructions
            ),
            result,
        ),
    )
    setattr(
        result,
        "native_circuit",
        partial(lambda self: to_native_func(self.circuit()), result),
    )

    return result
