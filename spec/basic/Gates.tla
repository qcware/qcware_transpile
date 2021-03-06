---- MODULE Gates ----
EXTENDS Sequences, TLC, Helpers


(* This module doesn't do very much; it's primarily a way of setting
up a few test values and to show you can get testable behaviour
from a few model gates.  A far better solution would be a large
exploration of a state space without concrete examples, but this
satisfices for now. *)

(* We pretend we are translating from a circuit space A of qubits
to a circuit space B of qubits (IE, that both "architectures"
have differently-labeled qubits), although this isn't important
for the moment *)
QUBITS_A == {0,1,2,3} \* Set of qubit identifiers for system A
QUBITS_B == {4,5,6,7} \* Set for system B

\* Gates as well should be handled by constants; these are just examples for now.
(* We make a distinction that isn't really shown here, that what follows is not
a "gate" but a "gate definition" in that it only specifies the name, names
of parameters, and IDs of qubits.  Later we will "bind" the gatedef either by
specifying the parameters to instantiate a "gate" (not really applied in this
spec) or by binding the IDs to make a "pattern" *)
X_A == [name |-> "X_A", parameters |-> {}, qubitIds |-> << 0 >> ] \* One qubit, no params
H_A == [name |-> "H_A", parameters |-> {}, qubitIds |-> << 1 >> ] \* same
SWAP_A == [name |-> "SWAP_A", parameters |-> {}, qubitIds |-> << 2, 3 >> ] \* Two qubits, no params
RZ_A == [name |-> "RZ_A", parameters |-> {"theta"}, qubitIds |-> << 0 >>] \* one qubit, one param
\* We also include one gate which shouldn't have a translation
UNTRANSLATABLE_A == [name |-> "UNTRANSLATABLE_A", parameters |-> {}, qubitIds |-> << 0 >> ]
\* The set of all expressible gates
GATES_A == {X_A,H_A,SWAP_A,RZ_A, UNTRANSLATABLE_A}
\* The set of all legal parameters for any parameter in GATES_A; this is
\* fictional but a subset given to generate test cases.  It would ideally
\* be a model parameter rather than specified here.
PARAMETER_VALUES_A == { 40, 50 }

(* We now repeat the exercise with architecture B *)
X_B == [name |-> "X_B", parameters |-> {}, qubitIds |-> << 4 >> ]
H_B == [name |-> "H_B", parameters |-> {}, qubitIds |-> << 5 >> ]
CX_B == [name |-> "CX_B", parameters |-> {}, qubitIds |-> << 6, 7 >> ]
RZ_B == [name |-> "RZ_B", parameters |-> {"theta_b"}, qubitIds |-> << 0 >> ]
GATES_B == {X_B,H_B, CX_B, RZ_B}
PARAMETER_VALUES_B == {60, 70}


NumGateQubits(gate) == Len(gate.qubitIds)


====
