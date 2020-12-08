------------------------------ MODULE MatchInstructionSequences ------------------------------
EXTENDS Sequences, Integers, Helpers, TLC, Gates

(* Some terminology:

A gatedef defines a name and the domains of parameters and bit ids.
A gate, then, is a gatedef with parameter bindings (not terribly useful)
A sequence of gates paired with bit bindings but with some or no parameter bindings is a pattern
An instruction pairs a gate with parameter bindings and bit id bindings
A sequence of instructions is a circuit
A replacement is a circuit, but the parameter bindings, rather than to values,
are to references in the source circuit
 *)


(* A Bit Binding Signature is the set of all gate bindings (within
a sequence, this is the tuple << instruction_index, QubitId >> which are
bound in a circuit to the same qubit *)

\* Find the bit bindings for a given instruction
BitBindings(Instruction) ==
  LET bitIds == Instruction[1].qubitIds
      bitAssignments == Instruction[3]
  IN MapSeqToSeq(bitIds, bitAssignments)

(* append an index to each member of the domain of f; this allows us to
convert a function mapping one standalone instruction (mapping x->f(x))
to a mapping of each instruction in a circuit ( <index,x> -> f(x) ) *)
PrependIndexToDomain(index, f) ==
  LET NewDomain == { << index, x >> : x \in DOMAIN f } IN
  [ y \in NewDomain |-> f[y[2]] ]

(*
The set of forward bit bindings for a sequence of instructions.
"Forward" bit bindings map from tuples of (index, bit_id):> bit_assignment;
in other words, if a circuit was the gate
[name |-> "SWAP_A", parameters |-> {}, qubitIds |-> << 2,3 >>] applied to
bit binding << 0, 1 >>, the basic bindings for the instruction would be
( 2:>0, 3:> 1), but since that is the first instruction, the full bindings
would be ( << 1,2 >> :> 0, << 1,3 >> :> 1 )
*)
SeqBitBindings(s) ==
  MergeFunctionSet({PrependIndexToDomain(n, BitBindings(s[n])): n \in 1..Len(s)})

(* the set of bindings in a sequence.  A BitBindingSignature is the set of
sets of all bits in the circuit pattern bound to the same bits.

In other words, in the swap circuit CX(0,1), CX(1,0), CX(0,1), the bit binding
signature would be { { <<1,1>>, <<2,2>>, <<3,1>> }, { <<1,2>>, <<2,1>>, <<3,2>> } } *)

BitBindingSignature(circuit) ==
  LET forwardBindings == SeqBitBindings(circuit) IN
  LET reverseBindings == ReverseFunction(forwardBindings) IN
  Range(reverseBindings) \*SetReverseBindings)
  
\* the sequence of gate names in the circuit
GateNames(circuit) ==
  [ x \in 1..Len(circuit) |-> circuit[x][1].name ]

\* The sequence of parameter mappings in the circuit
ParameterMappings(circuit) ==
  [ x \in 1..Len(circuit) |-> circuit[x][2] ]

\* Whether or not parameter mappings match
ParameterMappingsMatch( mappingsA, mappingsB ) ==
  /\ DOMAIN mappingsA = DOMAIN mappingsB
  /\ \A index \in DOMAIN mappingsA:
    IsSubfunction( mappingsA[index], mappingsB[index] )

(*
whether one circuit matches another on everything except the actual bits
bound to the inputs.  A pattern on the left matches if every defined
parameter on the left matches the same defined parameter on the right;
if no parameters are defined on the left, the parameters match.
If two circuits have the same sequence of gates and the same bit bindings, and
the same parameter bindings, they are equivalent.  If one circuit (the pattern)
has the same sequence of gates and same bit bindings but fewer parameter bindings
but those parameter bindings match, the pattern matches the circuit
*)

PatternMatchesCircuit(pattern, circuit) ==
  /\ GateNames(pattern) = GateNames(circuit)
  /\ ParameterMappingsMatch(ParameterMappings(pattern), ParameterMappings(circuit))
  /\ BitBindingSignature(pattern) = BitBindingSignature(circuit)
  
TEST_A == << << [name |-> "SWAP_A", parameters |-> {}, qubitIds |-> <<2, 3>>],
            << >>,
            <<0, 1>> >>,
         << [name |-> "X_A", parameters |-> {}, qubitIds |-> <<0>>],
            << >>,
            <<0>> >> >>
TEST_B == << << [name |-> "SWAP_A", parameters |-> {}, qubitIds |-> <<2, 3>>],
            << >>,
            <<1, 0>> >>,
         << [name |-> "X_A", parameters |-> {}, qubitIds |-> <<0>>],
            << >>,
            <<0>> >> >>

\* Creates a one-instruction circuit from a gate, with an empty function for
\* parameter mappings.  
\* We're also taking the non-tla route that circuits begin with bit 0, and
\* are numbered sequentially from there
CircuitFromGate(g) ==
  << << g, EMPTYFUNC, [ x \in 1..Len(g.qubitIds) |-> x-1 ] >> >>


TEST_PATTERN_A == << << SWAP_A, EMPTYFUNC, << 0,1 >> >>,
                   << RZ_A, EMPTYFUNC, << 0 >> >> >>
TEST_MATCH_A == << << SWAP_A, EMPTYFUNC, << 1,0 >> >>,
                   << RZ_A, "theta_a" :> 2, << 0 >> >> >>
TEST_REPLACEMENT_A == << << CX_B, EMPTYFUNC, << 0, 1 >> >>,
                       << CX_B, EMPTYFUNC, << 1, 0 >> >>,
                       << CX_B, EMPTYFUNC, << 0, 1 >> >>,
		       << RZ_B, "theta_b" :> << 2, "theta_a" >>, << 0 >> >> >>

\* a replacement is valid for a pattern if the replacement addresses a subset of the
\* qubits addressed by the pattern using the same IDs.
ReplacementValidForPattern(pattern, replacement) ==
  LET pattern_qubits == UNION { Range(pattern[x][3]): x \in DOMAIN pattern }
      replacement_qubits == UNION { Range(replacement[x][3]): x \in DOMAIN replacement } IN
  replacement_qubits \subseteq pattern_qubits

\* Remap the replacement instruction to the parameters and qubit IDs used by the circuit.
\* The replacement qubit maps map from the replacement/pattern to the circuit
RemapReplacementInstruction( ReplacementQubitMap, ReplacementParameterMap, instr ) ==
  LET parameters == [ x \in DOMAIN instr[2] |-> ReplacementParameterMap[ instr[2][x][1] ][ instr[2][x][2] ] ]
      newQubitIds == [ x \in 1..Len(instr[3]) |-> ReplacementQubitMap[ instr[3][x] ] ]
  IN
  << instr[1], parameters, newQubitIds >>

\* Create a replacement for a circuit.  The circuit input is a sequence of
\* instructions; the replacement is a circuit with bindings for its
\* unbound parameters and its replacement qubit mapping.
\* the qubit binding is achieved by matching forward bindings from the
\* pattern to the circuit.
CircuitReplacement(pattern, circuit, replacement) ==
  LET
      \* A map from the bindings in the pattern to the bindings in the circuit, in other words
      \* if the pattern has qubit IDs 0,1 and the circuit has corresponding qubit ids 3,4,
      \* the map is  0:>3 @@ 1:>4
      replacementQubitMap == MapRangeToRange( SeqBitBindings(pattern), SeqBitBindings(circuit) )
      replacementParameterMap == ParameterMappings(circuit)
  IN
  [ x \in 1..Len(replacement) |-> RemapReplacementInstruction( replacementQubitMap, replacementParameterMap, replacement[x] ) ]


\* Replace everything in this circuit with anything in the translations that matches
\* the whole circuit.  Precondition: the circuit must match something in the translations!
CircuitReplacementFromTranslations(circuit, translations) ==
  LET matches == { x \in translations: PatternMatchesCircuit(x.pattern, circuit) } IN
  \* right now, choose any suitable translation without weight/cost
  LET match == CHOOSE x \in matches: TRUE IN
  CircuitReplacement(match.pattern, circuit, match.replacement)
=============================================================================
\* Modification History
\* Created Wed Dec 2 15:13:39 CST 2020 by vputz
