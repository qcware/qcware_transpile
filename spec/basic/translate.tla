---- MODULE translate ----
EXTENDS Sequences, Integers

QUBITS_A == {0,1,2,3} \* Set of qubit identifiers for system A
QUBITS_B == {4,5,6,7}
x == [a |-> 1, b |-> {2, 3}]

\* Gates as well should be handled by constants; these are just examples for now.
X_A == [name |-> "X", numQubits |-> 1]
H_A == [name |-> "H", numQubits |-> 2]
SWAP_A == [name |-> "SWAP", numQubits |-> 2]
GATES_A == {X_A,H_A,SWAP_A}

X_B == [name |-> "X", numQubits |-> 1]
H_B == [name |-> "H", numQubits |-> 2]
CX_B == [name |-> "CX", numQubits |-> 2]
GATES_B == {X_B,H_B, CX_B}

SeqOfLengthN(S, n) == UNION {[(1..n) -> S]}

(* Initially model instructions as abstract application of gates
to sequences of qubits *)

InstructionsForGate(gate, qubits) ==
  { << gate, bits >> : bits \in SeqOfLengthN(qubits, gate.numQubits) }

INSTRUCTIONS_A ==
  { InstructionsForGate(gate, QUBITS_A) : gate \in GATES_A }

INSTRUCTIONS_B ==
  { InstructionsForGate(gate, QUBITS_B) : gate \in GATES_B }

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
