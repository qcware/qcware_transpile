
------------------------------ MODULE Translate ------------------------------
EXTENDS Integers, TLC, Sequences, MatchInstructionSequences, Instructions

CIRCUITS_A_MAX_LENGTH == 2
\* learntla.com/tla/functions
CIRCUITS_A == UNION { [1..m -> INSTRUCTIONS_A]: m \in 1..CIRCUITS_A_MAX_LENGTH }


SingleGateTranslations ==
  LET SGT(ga, gb) ==
    [ pattern |-> CircuitFromGate(ga),
      replacement |-> CircuitFromGate(gb) ]
  IN
    { SGT(H_A, H_B), SGT(X_A, X_B) }

MultiGateTranslations ==
{
  [ pattern |-> << << RZ_A, EMPTYFUNC, << 0 >> >> >>,
    replacement |-> << << RZ_B, "theta_b" :> << 1, "theta" >>, << 0 >> >> >> ],

  [ pattern |-> CircuitFromGate(SWAP_A),
    replacement |-> << << CX_B, EMPTYFUNC, << 0, 1 >> >>,
                     << CX_B, EMPTYFUNC, << 1, 0 >> >>,
                     << CX_B, EMPTYFUNC, << 0, 1 >> >> >> ]
}

Translations ==
  SingleGateTranslations \cup MultiGateTranslations


(* Let us make here a distinction between two different types
of circuit remappings.

A translation is the simplest; a translation table will have
source patterns each consisting of only one gate with no parameter
bindings, which translate into a replacement of one or more gates.
In this way the translation algorithm is easy (there should only be
one translation rule that matches a given step in the sequence)
and the translated circuit must always have a length equal to or
greater than the source circuit.

An optimization is more complex, because multiple patterns may
apply, and source patterns can be longer, so the target element
could be one or more gates.  This is much less predictable and may
require multiple passes.

We will thus here model just translation and have a separate
spec for optimization.
*)

StepIsTranslatable(s, translations) ==
  \E x \in Translations : PatternMatchesCircuit(x.pattern, <<s>>)

CircuitIsTranslatable(circuit, translations) ==
  \A x \in DOMAIN circuit : StepIsTranslatable(circuit[x], translations)


(* --algorithm Translate
variables
  circuit_a \in CIRCUITS_A;
  circuit_b = << >>;
  index = 1;
begin
  check_translatable:
  if CircuitIsTranslatable(circuit_a, Translations) then
  translate_circuit:
    while index < Len(circuit_a) do
    translate_instruction:
      circuit_b := circuit_b \o CircuitReplacementFromTranslations( << circuit_a[index] >> , Translations );
      index := index + 1;
    end while;
  else
    skip;
  end if;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7ce0fca01f83a1ba0c6b6428a7dd5d47
VARIABLES circuit_a, circuit_b, index, pc

vars == << circuit_a, circuit_b, index, pc >>

Init == (* Global variables *)
        /\ circuit_a \in CIRCUITS_A
        /\ circuit_b = << >>
        /\ index = 1
        /\ pc = "check_translatable"

check_translatable == /\ pc = "check_translatable"
                      /\ IF CircuitIsTranslatable(circuit_a, Translations)
                            THEN /\ pc' = "translate_circuit"
                            ELSE /\ TRUE
                                 /\ pc' = "Done"
                      /\ UNCHANGED << circuit_a, circuit_b, index >>

translate_circuit == /\ pc = "translate_circuit"
                     /\ IF index < Len(circuit_a)
                           THEN /\ pc' = "translate_instruction"
                           ELSE /\ pc' = "Done"
                     /\ UNCHANGED << circuit_a, circuit_b, index >>

translate_instruction == /\ pc = "translate_instruction"
                         /\ circuit_b' = circuit_b \o CircuitReplacementFromTranslations( << circuit_a[index] >> , Translations )
                         /\ index' = index + 1
                         /\ pc' = "translate_circuit"
                         /\ UNCHANGED circuit_a

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == check_translatable \/ translate_circuit \/ translate_instruction
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4a0f3b8e0e14586b43e3e1fbadea7cf8


=============================================================================
\* Modification History
\* Created Mon Nov 30 15:13:39 CST 2020 by vputz
