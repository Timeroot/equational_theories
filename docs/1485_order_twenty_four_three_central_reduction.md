# The three-central-vertex reduction at order twenty-four

Research note, 18 September 2026. This gives the complete incidence
reduction used by the subsequent
[three-central exclusion argument](1485_order_twenty_four_three_central.md).
The results are pen-and-paper proofs, not Lean declarations.

**Theorem.** Suppose an E1485 magma has order 24, minimum translation
degree three, and exactly three central vertices. Write `Z,A,B,T` for
its degree classes `3,4,6,8`. Then its class sizes are either

\[
 (|Z|,|A|,|B|,|T|)=(3,6,6,9)
 \quad\text{or}\quad (3,9,3,9).
\]

Every `A` vertex has three top neighbors and one sharp `B` neighbor
in each direction. Its top predecessor and successor sets are permutation
transversals of the central `3×3` grid. All predecessor transversals
have one parity and all successor transversals have the opposite parity.
Each of the three transversals of either parity occurs with the same
multiplicity, two or three respectively in the two cases above.

The [finite structure](1485_graph_research.md),
[strict degree descent](1485_image_research.md), and
[two-degree cardinality](1485_two_degree_lower_bound.md) theorems are
the background inputs.

## The central grid and the initial counts

Degree divisibility and complementary degrees leave `3,4,6,8` as the
possible degrees. Both middle degrees occur: otherwise the two-degree
cardinality theorem would give order 18, not 24.

For a top vertex `t`, let `k_t^-` and `k_t^+` be its numbers of
central predecessors and successors. Existence of sharp neighbors gives
`1≤k_t^-,k_t^+≤3`. Central incidence gives

\[
 \sum_t k_t^- =\sum_t k_t^+=9,
 \qquad \sum_t k_t^-k_t^+=9.
\]

Equality in `Σ k_t^-k_t^+≥Σ k_t^-` forces every `k_t^+=1`.
There are consequently nine top vertices; their predecessor degrees,
each at least one and summing to nine, are all one as well.

Label the central vertices `z_0,z_1,z_2`. Their nine products are
distinct top vertices, since each top has just one central predecessor
and successor. Thus write

\[
 t_{ij}=z_i*z_j,
 \qquad z_i\to t_{ij}\to z_j.
 \tag{1}
\]

The top endpoint pair `t_ij,t_kl` has a central middle precisely when
`j=k`, in which case that good middle is `z_j`.

Every vertex has exactly three top predecessors and three top successors.
Indeed its top predecessor set meets each central row exactly once;
these three rows partition the top set by (1). The dual argument uses
the three central columns.

A degree-four vertex therefore has exactly one non-top neighbor in each
direction. Its sharp neighbors have degree six, so these remaining
neighbors are its unique sharp `B` predecessor and successor.
Put `f=|A|`, `g=|B|`. Then

\[
 f+g=12,\qquad g\le f\le3g,
 \qquad 6\le f\le9,\quad 3\le g\le6.
 \tag{2}
\]

The inequalities count sharp `A,B` edges: each `A` contributes one,
and each `B` needs between one and three in either direction.

## Top profiles of `A` are permutation transversals

Fix `a∈A`, and write `P_a,Q_a` for its top predecessor and successor
sets. Centrality initially gives only

\[
 P_a=\{t_{i,p(i)}:i\in\{0,1,2\}\},\qquad
 Q_a=\{t_{q(j),j}:j\in\{0,1,2\}\},
 \tag{3}
\]

where the functions `p,q` need not yet be permutations.

For any `t∈P_a`, the three-element fiber `L_t^{-1}(a)` contains
the unique sharp `B` successor of `a`. Its other two elements must
be among the three top successors of `a`. Thus exactly one of the
three paths from `t` through `a` to `Q_a` is bad. Dually, for every
`v∈Q_a`, exactly one path from `P_a` through `a` to `v` is bad.

A bad path with middle `a` has good replacement of strictly smaller
degree, which must be central. Conversely, the presence of a central
middle makes its path through `a` bad by uniqueness. By (1), for
endpoints `t_ij,t_kl`, badness is therefore equivalent to `j=k`.

It follows that every value occurring among the `p(i)` occurs exactly
once among the `q(j)`. Dually, every value occurring among the `q(j)`
occurs exactly once among the `p(i)`. The two supports are equal, and
each value in their common support has multiplicity one in both lists.
Both lists have length three; hence they contain all three values.
Thus `p` and `q` are permutations.

Consequently both `P_a` and `Q_a` contain exactly one vertex from each
row and each column of the central grid. Such sets will be called its
permutation transversals.

## Predecessor and successor parities are opposite and constant

There are six permutation transversals, naturally indexed by the
permutations of three letters. Two transversals of opposite parity
meet in exactly one point. Two of the same parity meet in zero or
three points: their relative permutation is a nontrivial three-cycle
or the identity, respectively.

Let `F(a)∈B` be the unique sharp successor of `a∈A`, and let
`G(a)∈B` be its unique sharp predecessor. Both maps `F,G:A→B`
are surjective, because every `B` vertex has sharp neighbors in `A`.
A pair `a,c∈A` has a `B` middle exactly when

\[
 F(a)=G(c). \tag{4}
\]

Its only other possible ordinary middles are top vertices, in
`Q_a∩P_c`. If there is no `B` middle, the top middle must exist and
be unique: the good middle is top, and strict descent forbids another
bad middle of the same degree eight. Therefore

\[
 \operatorname{parity}(Q_a)=\operatorname{parity}(P_c)
 \quad\Longrightarrow\quad F(a)=G(c).
 \tag{5}
\]

Suppose both predecessor parities occurred. Choose `c_0,c_1` realizing
them. For every `a`, equation (5) identifies `F(a)` with one of the
two values `G(c_0),G(c_1)`, according to the parity of `Q_a`.
Surjectivity would imply `g≤2`, contrary to (2).
Thus all predecessor profiles have one parity. The dual argument shows
that all successor profiles also have one parity.

These two parities cannot agree. If they did, (5) would hold for
every `a,c`, making `F` constant and contradicting `g≥3` again.
This proves the claimed opposite parities. In particular every `A×A`
endpoint pair has exactly one ordinary top middle.

## Equal multiplicities and the two class-size possibilities

Let `P_0,P_1,P_2` be the three transversals of the predecessor parity,
and let `Q_0,Q_1,Q_2` be those of the successor parity. Each family
partitions the nine top vertices, and `|P_i∩Q_j|=1` for every `i,j`.
Let `c_i` count the `A` vertices with predecessor profile `P_i`,
and let `e_j` count those with successor profile `Q_j`.

Every top vertex has one central neighbor and three top neighbors in
each direction. Thus it has four neighbors in `A∪B` in each direction.
Ordinary degree balance and reciprocal-degree balance imply that its
number of `A` successors equals its number of `A` predecessors:
if their difference is `u` and the corresponding `B` difference is
`v`, the two equations are `u+v=0` and `u/4+v/6=0`, hence `u=v=0`.

At the unique top vertex in `P_i∩Q_j`, these two `A` counts are
`c_i` and `e_j`. Hence `c_i=e_j` for every pair `i,j`. All six
counts are equal to one integer `c`, and `f=3c`.
Combining with `6≤f≤9` gives precisely

\[
 (f,g,c)=(6,6,2)\quad\text{or}\quad(9,3,3).
 \tag{6}
\]

In the first case every `B` sharp in-degree and out-degree is one:
each direction has total six edges among six `B` vertices.
In the second case they are all three, since the total is nine among
three vertices and each is at most three. This completes the reduction.

## A useful additional profile bound

Two distinct `A` vertices cannot have the same pair `(P_i,Q_j)` of
top profiles. In that three-by-three top endpoint rectangle, exactly
three pairs have central middles, since both profiles are permutation
transversals. The other six pairs have no central middle. A path
through an `A` vertex at any one of those pairs must be good: a bad
degree-four middle could only have a central replacement. Two distinct
such middles would contradict uniqueness.

Thus each profile pair occurs at most once. For `f=9`, all nine pairs
occur. For `f=6`, the profile multiplicities form a zero-one
three-by-three matrix with every row and column sum two, the complement
of a permutation matrix. This last fact is a further restriction, not
an exclusion of the six/six case.
