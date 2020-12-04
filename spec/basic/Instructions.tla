---- MODULE Instructions ----
EXTENDS Gates

(* Initially model instructions as abstract application of gates
to sequences of qubits with the proviso that the number of
bits in the bits tuple is equal to the number of qubits
usable by the gate.  We won't play with broadcasting etc here. *)

InstructionsForGate(gate, parameter_values, qubits) ==
  { << gate, parameter_mappings, bits >> : parameter_mappings \in [gate.parameters -> parameter_values], bits \in UniqSeqsOfLengthN(qubits, NumGateQubits(gate) ) }

INSTRUCTIONS_A ==
  UNION { InstructionsForGate(gate, PARAMETER_VALUES_A, QUBITS_A) : gate \in GATES_A }

INSTRUCTIONS_B ==
  UNION { InstructionsForGate(gate, PARAMETER_VALUES_B, QUBITS_B) : gate \in GATES_B }


====
