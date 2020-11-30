------------------------------ MODULE circuits ------------------------------
EXTENDS translate, Integers, TLC, Sequences

CIRCUITS_A_MAX_LENGTH == 3
\* learntla.com/tla/functions
CIRCUITS_A == UNION {[1..m -> INSTRUCTIONS_A]: m \in 1..CIRCUITS_A_MAX_LENGTH}

CircuitIsTranslatable(circuit) ==
   LET circuitGates == {circuit[x][1] : x \in DOMAIN circuit} IN
   \A x \in circuitGates: x \in TranslatableGates


(* --algorithm circuits
variables
  circuit_a \in CIRCUITS_A;
  circuit_b = << >>;
  translatable = FALSE;
  index = 1;
begin
  translatable := CircuitIsTranslatable(circuit_a);
  if translatable then
    while index < Len(circuit_a) do
      circuit_b := circuit_b \o TranslateInstruction(circuit_a[index]);
      index := index + 1;
    end while
  end if
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-353c190d49a42e366f527c8d203a14cd
VARIABLES circuit_a, circuit_b, translatable, index, pc

vars == << circuit_a, circuit_b, translatable, index, pc >>

Init == (* Global variables *)
        /\ circuit_a \in CIRCUITS_A
        /\ circuit_b = << >>
        /\ translatable = FALSE
        /\ index = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ translatable' = CircuitIsTranslatable(circuit_a)
         /\ IF translatable'
               THEN /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
         /\ UNCHANGED << circuit_a, circuit_b, index >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF index < Len(circuit_a)
               THEN /\ circuit_b' = circuit_b \o TranslateInstruction(circuit_a[index])
                    /\ index' = index + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << circuit_b, index >>
         /\ UNCHANGED << circuit_a, translatable >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-59347ccd22bea4bb6adfe30808b29de7


=============================================================================
\* Modification History
\* Created Mon Nov 30 15:13:39 CST 2020 by vputz
