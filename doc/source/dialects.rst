Dialects
========

A Dialect represents an abstract view of the sorts of gates one can
construct with a given toolkit.  The possible gates are determined
programmatically from inspection of the toolkit at run-time, allowing
for expansion as toolkits are more fully fleshed-out.

Quasar
------

.. automodule:: qcware_transpile.dialects.quasar
   :members: native_to_ir, ir_to_native, dialect, native_circuits_are_equivalent
   :imported-members:

Qiskit
------
      
.. automodule:: qcware_transpile.dialects.qiskit
   :members: native_to_ir, ir_to_native, dialect, native_circuits_are_equivalent
   :imported-members:

Pyzx
----

.. automodule:: qcware_transpile.dialects.pyzx
   :members: native_to_ir, ir_to_native, dialect, native_circuits_are_equivalent
   :imported-members:

QSharp
------

Note: to install the Q# dependencies, you must be certain to install the Q#
environment correctly; unlike the other dialects, Q# cannot be installed
cleanly with Pip; you will have to use Conda or external tools to install the
required dotnet environment (for example, on Ubuntu, the snapcraft solution
seems to work; see https://docs.microsoft.com/en-us/dotnet/core/install/linux-snap)
