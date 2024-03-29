"""
Modules and functions for the transpilation of circuits
"""
try:
    import importlib.metadata as importlib_metadata
except ModuleNotFoundError:
    import importlib_metadata  # type: ignore

__version__ = importlib_metadata.version(__name__)

from .exceptions import TranslationException
