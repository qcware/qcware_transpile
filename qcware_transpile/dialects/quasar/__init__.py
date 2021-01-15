"""
Functions and structures involved with extracting a usable
Dialect from quasar, and converting to and from Quasar
Circuits (and possibly returns)
"""
from .quasar_dialect import (dialect, native_to_ir, ir_to_native,
                             native_circuits_are_equivalent)
