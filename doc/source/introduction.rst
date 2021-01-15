Introduction
============

A number of quantum computing packages exist to allow the
user to create, adjust, optimize, edit, mangle, and eventually
evaluate quantum circuits.

Unfortunately, almost all of these do a little too much,
and sometimes it would be nice to use some features of one
package on a circuit built on another package--for example,
to create a circuit with one, transpile it to a new set of
gates with another, optimize with a third, and then execute
it with a fourth.

Eventually, much as with how the low-level virtual machine
(LLVM) project allows one to use many tools on an underlying
intermediate representation, the industry will settle on a
more universal IR.  In the meantime, this is one of many
tools to attempt to help bridge that gap.

Qcware-transpile takes the approach that right now no single
IR supports all the features of toolkits, so we create a
simple dialect for each, programmatically, representing the
circuit as a simple sequence.  From there, transformation rules
can "translate" one dialect to another, so a native-to-native
circuit translation may look like

native_a -> dialect_a -> translation rules -> dialect_b -> native_b

While qcware_transpile supports reasonably complex translation rules,
since it operates on sequences (rather than representing a circuit
internally as a directed acyclic graph) it itself is not well-suited
to complex optimization or transpilation (thus the name is somewhat
misleading); its main use is to be a fairly robust and well-tested
toolkit for translation between toolkits which themselves can be used
for more complex transformations.

