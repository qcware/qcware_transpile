---- MODULE translate ----
EXTENDS Sequences, Integers, TLC, FiniteSets, Gates, Helpers, Instructions




\* returns a function that maps elements of sequence 1 onto sequence 2.
\* If an item occurs more than once in seq1, only the first occurrence
\* is mapped, ie MapSeqToSeq(<<2,2>>, <<3,4>>) results in 2:>3
MapSeqToSeq(seq1, seq2) ==
  [ x \in Range(seq1) |-> seq2[FirstIndexOf(x, seq1)] ]

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

(* Translating an instruction is a bit tricky.  An instruction is a gate
with the qubitIds (on the gate) bound to qubits (in circuit A).  One must
then produce a sequence of instructions with the qubit IDs on gate(s) B
bound to qubit ids on circuit B.

This will map << gate, parameter_mappings, bits >>
to << << gate, parameter_mappings, bits >> .. >> *)
TranslateInstruction(inst) ==
  LET Gate_A == inst[1] IN
  LET Parameter_mappings_A == inst[2] IN
  LET Bits_A == inst[3] IN
  LET Translation == TranslateGate[<< Gate_A >>] IN
  LET dom_B == DOMAIN Translation IN
  [ x \in dom_B |-> << Translation[x].gate,
                   TranslateParameters(Parameter_mappings_A, Translation[x].parameterMap),
                   
                   MapBits(Bits_A, Gate_A.qubitIds, Translation[x].qubitMap, Translation[x].gate.qubitIds) >> ]
  

====
