import numpy
import parse
import pytest
import quasar
from hypothesis import assume, given, note, settings
from quasar.measurement import ProbabilityHistogram
from toolz.functoolz import thread_first

from qcware_transpile.circuits import reverse_circuit
from qcware_transpile.dialects import qsharp as qsharp_dialect
from qcware_transpile.dialects import quasar as quasar_dialect
from qcware_transpile.matching import simple_translate, translated_gates
from qcware_transpile.translations.quasar.to_qsharp import (
    native_is_translatable,
    translation_set,
)

from ...strategies.qsharp import measure_circuit, run_generated_circuit
from ...strategies.quasar import circuits, gates

ts = translation_set()
translatable_gatenames = [x.name for x in translated_gates(translation_set())]
translatable_circuits = circuits(1, 3, 1, 4, gates(gate_list=translatable_gatenames))


def quasar_statevector(circuit: quasar.Circuit):
    b = quasar.QuasarSimulatorBackend()
    sv = b.run_statevector(circuit)
    return sv


def qsharp_statevector(circuit: str):
    return run_generated_circuit(circuit)


@given(translatable_circuits)
@settings(deadline=None)
def test_translate_quasar_to_qsharp(quasar_circuit):
    assume(native_is_translatable(quasar_circuit))
    note(str(quasar_circuit))
    quasar_transpilation_circuit = quasar_dialect.native_to_ir(quasar_circuit)
    note(str(quasar_transpilation_circuit))
    # reverse the bit order in the ir quasar circuit
    # since quasar uses big-endian representation and
    # qsharp uses little-endian representation
    reversed_quasar_transpilation_circuit = reverse_circuit(
        quasar_transpilation_circuit
    )
    note(str(reversed_quasar_transpilation_circuit))
    qsharp_transpiled_circuit = simple_translate(
        ts, reversed_quasar_transpilation_circuit
    )
    note(str(qsharp_transpiled_circuit))
    qsharp_native_circuit = qsharp_dialect.ir_to_native(qsharp_transpiled_circuit)
    note(str(qsharp_native_circuit))
    sv_quasar = quasar_statevector(quasar_circuit)
    sv_qsharp = qsharp_statevector(qsharp_native_circuit)
    assert numpy.allclose(sv_quasar, sv_qsharp, atol=1e-06)


def test_measurement(shots=1000):
    circuit = quasar.Circuit().H(0).CX(0, 1).X(2)
    qsharp_circuit = thread_first(
        circuit,
        quasar_dialect.native_to_ir,
        # reverse the bit order in the ir quasar circuit
        # since quasar uses big-endian representation and
        # qsharp uses little-endian representation
        reverse_circuit,
        lambda x: simple_translate(translation_set(), x),
        qsharp_dialect.ir_to_native,
    )

    def binlist_from_binstr(binlist: str) -> str:
        # convert a string expressing a list of binary digits (e.g. '[1,1,1]')
        # into a string expressing a binary value (e.g. '111')
        return "".join(str(x[0]) for x in parse.findall("{:b}", binlist))

    def int_from_binstr(binstr: str) -> int:
        # convert a string expressing a binary value (e.g. '111')
        # into an integer (e.g. 7)
        return int(binstr, base=2)

    qsharp_result = measure_circuit(qc=qsharp_circuit, shots=shots)
    histogram = {
        # reverse the bit order of each key in the histogram
        # because although qsharp uses little-endian
        # (most significant digit first) for representing
        # states in the statevector, it returns measurements
        # in index order (least significant digit first)
        int_from_binstr(binlist_from_binstr(k)[::-1]): v
        for k, v in qsharp_result.items()
    }
    result = ProbabilityHistogram(
        nqubit=circuit.nqubit, nmeasurement=shots, histogram=histogram
    )
    # test circuit generates states (0, 0, 1) and (1, 1, 1)
    # with 50% probability each
    assert abs(result.histogram[1] - 0.5) < 0.1
