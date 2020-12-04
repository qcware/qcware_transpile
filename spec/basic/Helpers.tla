---- MODULE Helpers ----
EXTENDS FiniteSets, Integers, Sequences, TLC

\* The set of all items in a tuple
TupleMembers(t) == {t[x]: x \in 1..Len(t)}

\* All sequences of length n which can be made of the members of set S
SeqsOfLengthN(S, n) == UNION {[(1..n) -> S]}

\* The sequences (all permutations) of length n from members of set S where all members
\* of the sequence are unique
UniqSeqsOfLengthN(S, n) == {s \in SeqsOfLengthN(S, n): Cardinality(TupleMembers(s)) = n}

\* an empty function
EMPTYFUNC == [x \in {} |-> {}]

\* For small functions, the set of members in the range of the function
Range(f) == {f[x]: x \in DOMAIN f}

\* The set of indices of a given item within a sequence
IndicesOf(item, seq) == { x \in DOMAIN seq : seq[x] = item }

\* The first index of an item when it occurs in a sequence.  Undefined
\* if the item does not occur.
FirstIndexOf(item, seq) ==
  LET indices == IndicesOf(item, seq) IN
  CHOOSE x \in indices : \A y \in indices \ {x}: x < y

\* returns a function that maps elements of sequence 1 onto sequence 2.
\* If an item occurs more than once in seq1, only the first occurrence
\* is mapped, ie MapSeqToSeq(<<2,2>>, <<3,4>>) results in 2:>3
MapSeqToSeq(seq1, seq2) ==
  [ x \in Range(seq1) |-> seq2[FirstIndexOf(x, seq1)] ]


\* for a given function with domain D and range R, return a new function
\* which maps each value in range R to a set of source values in domain D
ReverseFunction(f) ==
  LET D == DOMAIN f
      R == Range(f) IN
    [ x \in R |-> { y \in D : f[y] = x } ]

\* learntla.com/tla/operators
\* Calls a reduce on a set of items given an operation, a set of items,
\* and a starting seed value
RECURSIVE SetReduce(_, _, _)

SetReduce(Op(_, _), S, value) ==
  IF S = {} THEN value
  ELSE LET s == CHOOSE s \in S: TRUE IN
     SetReduce(Op, S \ {s}, Op(s, value))

\* Given a set of functions, appends them into one function
MergeFunctionSet(S) ==
  SetReduce(@@, S, EMPTYFUNC)

\* poorly named; returns the set of ranges for the functions in S
\* for which x is defined on the domain
SetFunctionCall(x, S) ==
  LET definedFunctions == { f \in S : x \in DOMAIN f } IN
  UNION { f[x] : f \in definedFunctions }

\* actually creates a function that returns SetFunctionCall(x,S)
\* for every item in the domain of all functions in S
SetFunction(S) ==
  LET SetDomain == UNION { DOMAIN f: f \in S } IN
  [ x \in SetDomain |-> SetFunctionCall(x, S) ]


====
