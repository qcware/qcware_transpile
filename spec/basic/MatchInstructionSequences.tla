------------------------------ MODULE MatchInstructionSequences ------------------------------
EXTENDS translate, Sequences

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
  {PrependIndexToDomain(n, BitBindings(s[n])): n \in 1..Len(s)}

\* for a given function with domain D and range R, return a new function
\* which maps each value in range R to a set of source values in domain D
ReverseFunction(f) ==
  LET D == DOMAIN f
      R == Range(f) IN
    [ x \in R |-> { y \in D : f[y] = x } ]

\* learntla.com/tla/operators
RECURSIVE SetReduce(_, _, _)

SetReduce(Op(_, _), S, value) ==
  IF S = {} THEN value
  ELSE LET s == CHOOSE s \in S: TRUE IN
     SetReduce(Op, S \ {s}, Op(s, value))

MergeFunctionSet(S) ==
  SetReduce(@@, S, EMPTYFUNC)

\* poorly named; returns the set of ranges for the functions in S
\* for which x is defined on the domain
SetFunctionCall(x, S) ==
  LET definedFunctions == { f \in S : x \in DOMAIN f } IN
  UNION { f[x] : f \in definedFunctions }

SetFunction(S) ==
  LET SetDomain == UNION { DOMAIN f: f \in S } IN
  [ x \in SetDomain |-> SetFunctionCall(x, S) ]

\* the set of bindings in a sequence
BitBindingSignature(circuit) ==
  LET forwardBindings == SeqBitBindings(circuit) IN
  LET reverseBindings == {ReverseFunction(f): f \in forwardBindings} IN
  LET SetReverseBindings == SetFunction(reverseBindings)
  IN
  Range(SetReverseBindings)
  

GateNames(circuit) ==
  [ x \in 1..Len(circuit) |-> circuit[x][1].name ]

ParameterMappings(circuit) ==
  [ x \in 1..Len(circuit) |-> circuit[x][2] ]

\* whether one circuit matches another on everything except the actual bits
\* bound to the inputs
CircuitsMatch(circuit_A, circuit_B) ==
  /\ GateNames(circuit_A) = GateNames(circuit_B)
  /\ ParameterMappings(circuit_A) = ParameterMappings(circuit_B)
  /\ BitBindingSignature(circuit_A) = BitBindingSignature(circuit_B)
  
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
=============================================================================
\* Modification History
\* Created Wed Dec 2 15:13:39 CST 2020 by vputz
