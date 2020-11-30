---- MODULE translate ----
EXTENDS Sequences, Integers, TLC

QUBITS_A == {0,1,2,3} \* Set of qubit identifiers for system A
QUBITS_B == {4,5,6,7}

\* Gates as well should be handled by constants; these are just examples for now.
X_A == [name |-> "X_A", qubitIds |-> << 0 >> ]
H_A == [name |-> "H_A", qubitIds |-> << 1 >> ]
SWAP_A == [name |-> "SWAP_A", qubitIds |-> << 2, 3 >> ]
UNTRANSLATABLE_A == [name |-> "UNTRANSLATABLE_A", qubitIds |-> << 0 >> ]
GATES_A == {X_A,H_A,SWAP_A, UNTRANSLATABLE_A}

X_B == [name |-> "X_B", qubitIds |-> << 4 >> ]
H_B == [name |-> "H_B", qubitIds |-> << 5 >> ]
CX_B == [name |-> "CX_B", qubitIds |-> << 6, 7 >> ]
GATES_B == {X_B,H_B, CX_B}

SeqOfLengthN(S, n) == UNION {[(1..n) -> S]}

NumGateQubits(gate) == Len(gate.qubitIds)

(* Initially model instructions as abstract application of gates
to sequences of qubits with the proviso that the number of
bits in the bits tuple is equal to the number of qubits
usable by the gate.  We won't play with broadcasting etc here. *)

InstructionsForGate(gate, qubits) ==
  { << gate, bits >> : bits \in SeqOfLengthN(qubits, NumGateQubits(gate) ) }

INSTRUCTIONS_A ==
  { InstructionsForGate(gate, QUBITS_A) : gate \in GATES_A }

INSTRUCTIONS_B ==
  { InstructionsForGate(gate, QUBITS_B) : gate \in GATES_B }

(* A gate translation maps a source gate to a sequence of gates.  This necessitates,
for each destination gate, a translation of qubit_ids.

The qubit map maps from B to A, which sounds unintuitive but works correctly.

Domain(qubitMap) = Range(gate.qubitIds)

This definition should be made more generic of course *)
TranslateGate == 
  [ X_A |-> << [gate |-> X_B, qubitMap |-> 4:>0] >>,
    H_A |-> << [gate |-> H_B, qubitMap |-> 5:>1] >>,
    SWAP_A |-> << [gate |-> CX_B, qubitMap |-> 6:>2 @@ 7:>3 ],
                [gate |-> CX_B, qubitMap |-> 7:>2 @@ 6:>3 ],
		[gate |-> CX_B, qubitMap |-> 6:>2 @@ 7:>3 ]>>]

TranslatableGates == DOMAIN TranslateGate

Range(f) == {f[x]: x \in DOMAIN f}
IndicesOf(item, seq) == { x \in DOMAIN seq : seq[x] = item }
FirstIndexOf(item, seq) ==
  LET indices == IndicesOf(item, seq) IN
  CHOOSE x \in indices : \A y \in indices \ {x}: x < y

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

(* Translating an instruction is a bit tricky.  An instruction is a gate
with the qubitIds (on the gate) bound to qubits (in circuit A).  One must
then produce a sequence of instructions with the qubit IDs on gate(s) B
bound to qubit ids on circuit B.  This will map << gate, bits >> to << << gate, bits >> .. >> *)
TranslateInstruction(inst) ==
  LET Gate_A == inst[1] IN
  LET Bits_A == inst[2] IN
  LET Translation == TranslateGate[Gate_A.name] IN
  LET dom_B == DOMAIN Translation IN
  [ x \in dom_B |-> << Translation[x].gate, MapBits(Bits_A, Gate_A.qubitIds, Translation[x].qubitMap, Translation[x].gate.qubitIds) >> ]
  

====
---- MODULE Circuit ----

CONSTANTS

TargetQC

====
