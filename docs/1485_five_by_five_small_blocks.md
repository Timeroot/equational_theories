# Five-by-five three-regular intersection matrices of small sets

Research note, 20 September 2026. This is an analytic finite-set
lemma. It uses neither magma axioms nor enumeration.

Let `C_1,…,C_5` and `P_1,…,P_5` be nonempty sets of size
at most two, repetitions allowed. Suppose

\[
K_{ij}=|C_i\cap P_j|\in\{0,1\},
\qquad \sum_jK_{ij}=\sum_iK_{ij}=3.
\]

**Theorem.**

1. If a row set is singleton, at least three column sets are
   pairs. Dually, a singleton column set forces at least three
   row pairs.
2. If both families contain a singleton, the two-regular bipartite
   graph of `J−K` is the disjoint union of a four-cycle and
   a six-cycle. In particular it is not a ten-cycle.

No bound on the ground-set size is needed. A singleton on just
one side does **not** force the cycle splitting, even with only
six labels. Both families can also have four pairs and one
singleton, even with only five labels.

## 1. A singleton requires three opposite pairs

Suppose `C_1={x}`. Precisely three column sets contain `x`.
At most two row sets contain `x`: three such rows and three
such columns would form an all-one `3×3` block. Regularity
would isolate that block, leaving two rows which need three
neighbors among just two remaining columns, a contradiction.

Each of the three columns containing `x` must therefore contain
another label, since a singleton column `{x}` would have column
sum at most two. These three column sets are pairs. The dual
argument proves the other assertion.

## 2. Two singleton families rule out the ten-cycle

The complement is a simple two-regular bipartite graph with five
vertices on each side. Its only possible cycle decompositions are
a ten-cycle or a four-cycle plus a six-cycle.

Suppose the complement were a ten-cycle, and take `C_1={x}`.
Every row containing `x` has the same three neighbors, since
those already exhaust its degree. A ten-cycle has no two rows
with identical complement neighborhoods. Thus `x` occurs in
exactly one row set.

After reindexing, the three columns containing `x` are

\[
\{x,z_1\},\quad\{x,z_2\},\quad\{x,z_3\}.
\]

Each `z_i` occurs in exactly two other row sets. The labels
`z_1,z_2,z_3` are distinct: equal labels would give identical
columns, also impossible in a ten-cycle.

Now let a column set be the singleton `{y}`. Its column sum
requires three occurrences of `y` among the row sets. Hence
`y` differs from `x` and from every `z_i`, whose occurrence
counts are one and two. All those occurrences lie in the four
rows other than `C_1`. Those four sets would contain six
occurrences of the three `z_i` plus three occurrences of `y`:
nine memberships in sets with total capacity eight. This is
impossible, proving the cycle splitting.

## 3. Sharpness and limits

Three pairs on each side suffice. On five distinct labels use

\[
\begin{aligned}
(C_i)&=(\{x\},\{x\},\{y,z_1\},\{y,z_2\},\{y,z_3\}),\\
(P_j)&=(\{x,z_1\},\{x,z_2\},\{x,z_3\},\{y\},\{y\}).
\end{aligned}
\]

A singleton row without a singleton column does not suffice
for the splitting. On six distinct labels, use

\[
\begin{aligned}
(C_i)&=(\{x\},\{z_1,z_2\},\{z_2,z_3\},\{z_1,a\},\{z_3,b\}),\\
(P_j)&=(\{x,z_1\},\{x,z_2\},\{x,z_3\},\{z_3,a\},\{z_1,b\}).
\end{aligned}
\]

Its intersection matrix is

\[
\begin{pmatrix}
1&1&1&0&0\\
1&1&0&0&1\\
0&1&1&1&0\\
1&0&0&1&1\\
0&0&1&1&1
\end{pmatrix},
\]

whose complement is a ten-cycle.

Nor does the presence of both singleton types force two
singletons in one family. On five distinct labels use

\[
\begin{aligned}
(C_i)&=(\{y,t\},\{y,t\},\{x\},\{y,z\},\{z,w\}),\\
(P_j)&=(\{x,t\},\{y\},\{t,w\},\{x,z\},\{x,z\}).
\end{aligned}
\]

Both families have four pairs and one singleton. The matrix is
three-regular and its complement splits as required. The singleton
row and singleton column lie in the six-cycle component, not
the four-cycle component. Thus that stronger classification is
false even below the six-label bound relevant to applications.

## Application to degree-seven first outputs

For minimum degree four and six central vertices, a degree-seven
first top output with five top neighbors has a three-regular
matrix of this form whenever its two central-block families have
size at most two. If both families contain a singleton, each
must therefore have at least three pairs and the complement
must split into a four-cycle and a six-cycle.

There is a stronger, separate argument when **all globally
occurring** central blocks have size at most two: the
[small-block first-output theorem](1485_small_central_blocks_first_output_gap.md)
excludes first degree seven altogether. The present local lemma
still applies to profiles in global configurations containing
three-element blocks elsewhere.
