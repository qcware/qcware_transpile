---- MODULE translate ----
EXTENDS Sequences, Integers, TLC

QUBITS_A == {0,1,2,3} \* Set of qubit identifiers for system A
QUBITS_B == {4,5,6,7}
x == [a |-> 1, b |-> {2, 3}]

\* Gates as well should be handled by constants; these are just examples for now.
X_A == [name |-> "X_A", qubitIds |-> << 0 >> ]
H_A == [name |-> "H_A", qubitIds |-> << 1 >> ]
SWAP_A == [name |-> "SWAP_A", qubitIds |-> << 2, 3 >> ]
GATES_A == {X_A,H_A,SWAP_A}

X_B == [name |-> "X_B", qubitIds |-> << 4 >> ]
H_B == [name |-> "H_B", qubitIds |-> << 5 >> ]
CX_B == [name |-> "CX_B", qubitIds |-> << 6, 7 >> ]
GATES_B == {X_B,H_B, CX_B}

SeqOfLengthN(S, n) == UNION {[(1..n) -> S]}

NumGateQubits(gate) == Len(gate.qubitIds)

(* Initially model instructions as abstract application of gates
to sequences of qubits *)

InstructionsForGate(gate, qubits) ==
  { << gate, bits >> : bits \in SeqOfLengthN(qubits, NumGateQubits(gate) ) }

INSTRUCTIONS_A ==
  { InstructionsForGate(gate, QUBITS_A) : gate \in GATES_A }

INSTRUCTIONS_B ==
  { InstructionsForGate(gate, QUBITS_B) : gate \in GATES_B }

(* A gate translation maps a source gate to a sequence of gates.  This necessitates,
for each destination gate, a translation of qubit_ids *)
GateTranslations == 
  [ X_A |-> << [gate |-> X_B, qubitMap |-> 0:>4] >>,
    H_A |-> << [gate |-> H_B, qubitMap |-> 1:>5] >>,
    SWAP_A |-> << [gate |-> CX_B, qubitMap |-> 2:>6 @@ 3:>7 ],
                [gate |-> CX_B, qubitMap |-> 2:>7 @@ 3:>6 ],
		[gate |-> CX_B, qubitMap |-> 2:>6 @@ 3:>7 ]>>]

TranslateGateName == 
  LET GateNames_A == {gate.name: gate \in GATES_A} IN
  LET GateNames_B == {gate.name: gate \in GATES_B} IN
  CHOOSE f \in [ GateNames_A -> GateNames_B ] : TRUE

\* TranslateQubits == CHOOSE f \in [ 
TranslateInstruction == CHOOSE f \in [INSTRUCTIONS_A -> INSTRUCTIONS_B]: TRUE

====
---- MODULE Circuit ----

CONSTANTS

TargetQC

====
