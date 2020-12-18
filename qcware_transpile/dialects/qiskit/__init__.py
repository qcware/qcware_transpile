"""
Functions and structures to programatically construct a dialect
from inspection of the qiskit library
"""

from .qiskit_dialect import (dialect, native_to_circuit, circuit_to_native,
                             native_circuits_are_equivalent)
