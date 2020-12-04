------------------------------ MODULE MatchInstructionSequences ------------------------------
EXTENDS Sequences, Integers, Helpers, TLC

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

\* checks to see if f is a subfunction of g
IsSubfunction(f, g) ==
  /\ DOMAIN f \subseteq DOMAIN g
  /\ \A x \in DOMAIN f: f[x] = g[x]

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
CircuitFromGate(g) ==
  << g, EMPTYFUNC, 1..Len(g.qubitIds) >>


\* Create a replacement for a circuit.  The circuit input is a sequence of
\* instructions; the replacement is a circuit with bindings for its
\* unbound parameters and its replacement qubit mapping.
\* the qubit binding is achieved by matching forward bindings from the
\* pattern to the circuit.
ReplaceCircuitWith(pattern, replacement, circuit) == {}
=============================================================================
\* Modification History
\* Created Wed Dec 2 15:13:39 CST 2020 by vputz
