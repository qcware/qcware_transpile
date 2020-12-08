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

\* append an index to each member of the domain of f
PrependIndexToDomain(index, f) ==
  LET NewDomain == { << index, x >> : x \in DOMAIN f } IN
  [ y \in NewDomain |-> f[y[2]] ]

\* and the set of forward bit bindings for a sequence of instructions
SeqBitBindings(s) ==
  MergeFunctionSet({PrependIndexToDomain(n, BitBindings(s[n])): n \in 1..Len(s)})

\* the set of bindings in a sequence
BitBindingSignature(circuit) ==
  LET forwardBindings == SeqBitBindings(circuit) IN
  LET reverseBindings == ReverseFunction(forwardBindings) IN
  Range(reverseBindings) \*SetReverseBindings)
  

GateNames(circuit) ==
  [ x \in 1..Len(circuit) |-> circuit[x][1].name ]

ParameterMappings(circuit) ==
  [ x \in 1..Len(circuit) |-> circuit[x][2] ]

ParameterMappingsMatch( mappingsA, mappingsB ) ==
  /\ DOMAIN mappingsA = DOMAIN mappingsB
  /\ \A index \in DOMAIN mappingsA:
    IsSubfunction( mappingsA[index], mappingsB[index] )
\* whether one circuit matches another on everything except the actual bits
\* bound to the inputs.  A pattern on the left matches if every defined
\* parameter on the left matches the same defined parameter on the right;
\* if no parameters are defined on the left, the parameters match.
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
\* parameter mappings.  We may have to think about this.  By default, circuits
\* match regardless of their parameter mappings, but we may have to think
\* about this; there may be a case where a gate with a particular parameter
\* mapping could be remapped to another gate (for example, Rx(pi) == CX?)
\* We're also taking the non-tla route that circuits begin with bit 0
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
  \*RemapReplacementInstruction( replacementQubitMap, replacementParameterMap, replacement[4] )
  \*<< replacementQubitMap, replacementParameterMap, replacement[4] >>

CircuitReplacementFromTranslations(circuit, translations) ==
  LET matches == { x \in translations: PatternMatchesCircuit(x.pattern, circuit) } IN
  \* right now, choose any suitable translation without weight/cost
  LET match == CHOOSE x \in matches: TRUE IN
  CircuitReplacement(match.pattern, circuit, match.replacement)
=============================================================================
\* Modification History
\* Created Wed Dec 2 15:13:39 CST 2020 by vputz
