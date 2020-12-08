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

(* given a tuple of bit ids (for a gate in GATES_A), and a bitIdMap from
a gate translation in TranslateGate, and some tuple of bits representing
bits in the circuit, give the translation.

bitIds_A represents an ordinal map (by index) from Ids in Gate_A to bits in bits
bitIdMap represents a map from bitIds_A to bitIds_B

*)
MapBits( bits_A, bitIds_A, bitIdMap_BA, bitIds_B) ==
  LET dombits_A == DOMAIN bits_A IN
  LET dombits_B == DOMAIN bitIds_B IN
  LET bitmapping_A == MapSeqToSeq(bitIds_A, bits_A) IN
  [ x \in dombits_B |-> bitmapping_A[bitIdMap_BA[bitIds_B[x]]] ]

(* Given a map of parameter assignments for gate A, and a mapping
[ parameter_B |-> << parameter_A, [value_A |-> value_B] >> ],
return parameter_assignments_B *)
TranslateParameters( parameter_assignments_A, parameter_map_BA ) ==
  [ x \in DOMAIN parameter_map_BA |-> parameter_map_BA[x][2][parameter_assignments_A[parameter_map_BA[x][1]]] ]


====
