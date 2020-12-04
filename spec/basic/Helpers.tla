---- MODULE Helpers ----
EXTENDS FiniteSets, Integers, Sequences

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


====
