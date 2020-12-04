---- MODULE Gates ----
EXTENDS Sequences, TLC, Helpers

QUBITS_A == {0,1,2,3} \* Set of qubit identifiers for system A
QUBITS_B == {4,5,6,7}

\* Gates as well should be handled by constants; these are just examples for now.
X_A == [name |-> "X_A", parameters |-> {}, qubitIds |-> << 0 >> ]
H_A == [name |-> "H_A", parameters |-> {}, qubitIds |-> << 1 >> ]
SWAP_A == [name |-> "SWAP_A", parameters |-> {}, qubitIds |-> << 2, 3 >> ]
RZ_A == [name |-> "RZ_A", parameters |-> {"theta"}, qubitIds |-> << 0 >>]
UNTRANSLATABLE_A == [name |-> "UNTRANSLATABLE_A", parameters |-> {}, qubitIds |-> << 0 >> ]
GATES_A == {X_A,H_A,SWAP_A, UNTRANSLATABLE_A}
PARAMETER_VALUES_A == { 40, 50 }

X_B == [name |-> "X_B", parameters |-> {}, qubitIds |-> << 4 >> ]
H_B == [name |-> "H_B", parameters |-> {}, qubitIds |-> << 5 >> ]
CX_B == [name |-> "CX_B", parameters |-> {}, qubitIds |-> << 6, 7 >> ]
RZ_B == [name |-> "RZ_B", parameters |-> {"theta_b"}, qubitIds |-> << 0 >> ]
GATES_B == {X_B,H_B, CX_B}
PARAMETER_VALUES_B == {60, 70}


NumGateQubits(gate) == Len(gate.qubitIds)

(* A gate translation maps a source gate to a sequence of gates.  This necessitates,
for each destination gate, a translation of qubit_ids.

The qubit map maps from B to A, which sounds unintuitive but works correctly.  We
use the qubit IDs on the B side to "pull" the values on the A side.

Domain(qubitMap) = Range(gate.qubitIds)

This definition should be made more generic of course *)
TranslateGate == 
  << X_A >> :> << [gate |-> X_B, parameterMap |-> EMPTYFUNC, qubitMap |-> 4:>0] >> 
  @@ << H_A >> :> << [gate |-> H_B, parameterMap |-> EMPTYFUNC, qubitMap |-> 5:>1] >>
  @@ << RZ_A >> :> << [gate |-> RZ_B,
               parameterMap |-> [theta_b |-> << "theta_a",
	                                     CHOOSE x \in [PARAMETER_VALUES_A -> PARAMETER_VALUES_B]: TRUE >> ],
	       qubitMap |-> 0:>0] >>
  @@ << SWAP_A >> :> << [gate |-> CX_B, parameterMap |-> EMPTYFUNC, qubitMap |-> 6:>2 @@ 7:>3 ],
                [gate |-> CX_B, parameterMap |-> EMPTYFUNC, qubitMap |-> 7:>2 @@ 6:>3 ],
		[gate |-> CX_B, parameterMap |-> EMPTYFUNC, qubitMap |-> 6:>2 @@ 7:>3 ]>>

TranslatableGates == DOMAIN TranslateGate


====
