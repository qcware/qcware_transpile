Concepts
========

While most toolkits represent quantum circuit gates along with their
mathematical representations, at this level of abstraction we can take
a very high-level view.  All data structures are immutable once
constructed.

Gate Definitions
----------------

We represent a gate with a very simplistic approximation:
just enough information to recreate the gate in a toolkit
and provide enough information for translation.  Thus we only
care about three items for a GateDef:

* The gate *name* (such as `H`, `HGate`, `CX`, etc)
* The names of the gate's arguments (`theta`, `phi`)
* A set of bit IDs that the gate operates on

GateDefs can be bound in various ways:

* A gate with all arguments bound is a Gate
* A gate with all arguments and qubits bound is an Instruction
* A gate with *partial* (or full) argument bindings can be used as
  part of a pattern for matching.  This allows a translation rule to
  match, say, `RX(pi)` to a negation, while still mapping `RX({})` to
  other instructions.  This is not currently fully explored.

Dialects
--------

Dialects are simply a name and a set of GateDefs.

Circuits
--------

Circuits are comprised of a dialect name, a sequence of
instructions, and a set of bits that the circuit operates on.

TranslationRules
----------------

A TranslationRule is a pattern and a replacement, which encodes
rules for mapping arguments.

TranslationSet
--------------

And predictably, a TranslationSet represents a mapping from one
Dialect to another.
