# Further central-incidence restrictions at order twenty-four

Research note, 18 September 2026. These are pen-and-paper restrictions
on a hypothetical E1485 magma of order 24 and minimum degree three.
They do not constitute a complete exclusion of that order.

Use the notation and incidence identities in the
[large-central-class reduction](1485_order_twenty_four_large_central.md):
`Z,A,B,T` have degrees `3,4,6,8`, their sizes are `m,f,g,h`, and a
top vertex has central predecessor and successor counts `(k^-,k^+)`.
In particular

\[
 \sum k^- =\sum k^+=3m,\qquad \sum k^-k^+=m^2,
 \qquad 1\le k^-,k^+\le3.
 \tag{1}
\]

This note excludes `(m,h)=(4,8),(4,10),(5,11),(6,11),(6,12)`.
The elementary bounds also give `h≥8` for `m=4`, and `h≥9` for
`m=5,6`. Consequently the remaining top-class sizes in these three
central cases are

| Central cardinality `m` | Remaining top cardinalities `h` |
| --- | --- |
| 4 | 9 |
| 5 | 9, 10 |
| 6 | 9, 10 |

These are necessary remaining cases, not constructions.
In the remaining `m=4,h=9` case, the final section shows that all
degree-four vertices have sharp degree one, leaving only
`(f,g)=(6,5)` or `(7,4)`.

## Central rows and columns have prescribed weight patterns

Every central row consists of three top vertices, and their `k^+`
weights sum to `m`. Indeed their central successor sets partition `Z`,
by unique goodness. Dually, every central column has three `k^-`
weights summing to `m`. For the values under consideration the possible
unordered weight patterns are

\[
 \begin{array}{c|c}
 m&\text{patterns}\\\hline
 4&(1,1,2)\\
 5&(1,1,3),(1,2,2)\\
 6&(1,2,3),(2,2,2).
 \end{array} \tag{2}
\]

Every top vertex has at least one central predecessor and successor,
so it appears in these patterns.

The deficit variables `a=3−k^-`, `b=3−k^+` satisfy

\[
 \sum(a+b-ab)=12m-m^2-3h. \tag{3}
\]

For top types `(1,1),(3,3)` the summand is zero; it is one for
`(1,2),(2,1),(2,2),(2,3),(3,2)`, and two for `(1,3),(3,1)`.

Also `3k^+≤h` and `3k^-≤h`: the central outputs of a top
translation occupy that many top inputs. If `h≤8`, all central
weights are therefore at most two. For `m=5,h=8`, this contradicts

\[
 0\le\sum(2-k^-)(2-k^+)=m^2-12m+4h=-3.
\]

For `m=6,h=8`, it contradicts `Σk^+=18>16`. The general incidence
bound gives `h≥8` for `m=5,6`. For `m=4`, pattern (2) excludes
central weights three regardless of `h`, and the analogous nonnegative
sum is `Σ(2−k^-)(2−k^+)=4h−32`; hence `h≥8` in this case as well.

## Six central vertices and twelve top vertices

Here (3) vanishes. Thus all top weights are odd: each type is `(1,1)`
or `(3,3)`. But a central row has three such weights and their sum
must be six, impossible by parity.

## Six central vertices and eleven top vertices

Now (3) equals three. Pattern (2) requires every central row to
contain at least one top vertex of successor weight two. The total
number of such incidences is

\[
 I_2=\sum_{k^+=2} k^-\ge6.
\]

Each vertex with `k^+=2` contributes one to (3), so there are at
most three of them. There cannot be only two: to reach `I_2≥6`,
both would have type `(3,2)`, whose marginal differences sum to two.
The remaining one unit in (3) cannot cancel that difference. A type
of summand one has marginal difference at least minus one, and a
type of summand zero has marginal difference zero.

Thus there are three vertices with `k^+=2`, using all three units
in (3). Every other vertex has type `(1,1)` or `(3,3)`. The dual
condition `Σ_{k^-=2}k^+≥6` forces all three exceptional vertices
to have predecessor weight two as well. Equation (1) now gives
exactly

\[
 \text{six }(1,1),\qquad
 \text{three }(2,2),\qquad
 \text{two }(3,3). \tag{4}
\]

The total incidence at successor weight two is exactly six, so each
central row has pattern `(1,2,3)`, never `(2,2,2)`. The same holds
for columns. Hence the central predecessor sets of the two `(3,3)`
vertices partition `Z` into two triples, and their central successor
sets also partition `Z` into two triples. The three `(2,2)` vertices
likewise partition `Z` into predecessor pairs and successor pairs.

Each `(2,2)` predecessor pair must lie inside one of the predecessor
triples. Otherwise its two rows belong to different `(3,3)` rectangles;
its successor pair would have to avoid both disjoint successor triples,
which cover `Z`. This contradicts its nonemptiness.

But a partition into pairs cannot refine a partition into triples.
This excludes the case.

## Five central vertices and eleven top vertices

Equation (3) equals two. Equal marginal sums and their parity give
the following three profiles, by the same two-unit calculation used
in the large-central-class reduction:

| Common types | Remaining two vertices |
| --- | --- |
| eight `(1,1)`, one `(3,3)` | two `(2,2)` |
| eight `(1,1)`, one `(3,3)` | `(2,1)` and `(2,3)` |
| eight `(1,1)`, one `(3,3)` | `(1,2)` and `(3,2)` |

For the symmetric profile, the `(3,3)` vertex is a neighbor of three
central rows, which therefore have pattern `(1,1,3)`. The other two
central rows have pattern `(1,2,2)` and contain both `(2,2)` vertices.
The dual statement gives the same two central columns for these two
vertices. Their central rectangles are thus identical two-by-two
rectangles, contradicting unique goodness.

For the second profile, the three central columns reached by the
`(3,3)` vertex have incoming pattern `(1,1,3)`. The other two columns
have incoming pattern `(1,2,2)` and must both be reached by each of
the only two predecessor-weight-two vertices. One of these has type
`(2,1)` and central out-degree one, a contradiction. The third profile
is excluded dually.

## Four central vertices and ten top vertices

For `m=4`, pattern (2) excludes both central weights three. Write
`a,b,c,d` for the numbers of top types `(1,1),(1,2),(2,1),(2,2)`.
Equation (1) gives `b=c`, `b+2d=4`, and `a+2b+d=h`.
At `h=10` these imply

\[
 \text{eight }(1,1),\qquad\text{two }(2,2). \tag{5}
\]

A degree-four vertex has neighbors only in `B` and `T`. The weighted
top-incidence equation forces at least two top neighbors. Thus its
sharp degree is one or two. The sharp in-degree and out-degree agree,
by reciprocal-degree balance. Let `f_1,f_2` count these two types;
put `f=f_1+f_2`, so `g=10−f`.

An `A` vertex of sharp degree two has two top neighbors, of weights
two and two, in each direction. Thus its top predecessor and successor
sets are both exactly the two `(2,2)` top vertices. An `A` vertex
of sharp degree one has three top neighbors, with weights `(1,1,2)`.

At a top vertex, each central output consumes three top inputs. An
`A` output of sharp degree one consumes two top inputs; one of sharp
degree two consumes one. Summing this top-input bound over the two
`(2,2)` vertices gives

\[
 2f_1+2f_2\le8,
\]

because each sharp-degree-one `A` vertex has one such predecessor,
and each sharp-degree-two `A` vertex has both. Hence `f≤4`.
Every `B` vertex requires a sharp predecessor in `A`, so

\[
 10-f=g\le f_1+2f_2=2f-f_1.
\]

These inequalities force `f=4` and `f_1≤2`, hence `f_2≥2`.

Finally, two distinct sharp-degree-two `A` vertices cannot have those
same top predecessor and successor sets. Choose a top predecessor of
the first. Its three-element fiber at that `A` output contains the two
sharp `B` successors and one top successor, so there is a good top
endpoint pair through it. The second `A` vertex is another middle
for that pair, of the same degree four. It cannot be bad, by strict
degree descent, and cannot be good, by uniqueness. This contradiction
excludes `f_2≥2` and completes the claimed restrictions.

## Four central vertices and eight top vertices

At `m=4,h=8`, the central-weight equations used above give four top
vertices of type `(1,2)` and four of type `(2,1)`. Label the former
`U_i` by their unique central predecessor `z_i`, and the latter `V_j`
by their unique central successor `z_j`, where `i,j∈{1,2,3,4}`.
These labels are bijective because every central row has exactly one
top successor of successor weight two, and dually for columns.

Let `S_ij` indicate `U_i→z_j`. This is a four-by-four zero-one
matrix with all row and column sums two. Unique good paths with
central endpoints say

\[
 z_i\to V_j\quad\Longleftrightarrow\quad S_{ij}=0.
\]

The central-middle path-count matrix on the top vertices, in the order
`U,V`, consequently has blocks

\[
 K=\begin{pmatrix}
 S&2J_4-S^2\\ I_4&J_4-S
 \end{pmatrix}. \tag{6}
\]

All its entries are zero or one. Thus every entry of `S²` is at
least one. Its row sums are four, so `S²=J_4`, and in particular

\[
 K_{U,V}=J_4. \tag{7}
\]

Suppose an `A` vertex has sharp degree one. Its three top predecessors
have predecessor weights `(1,1,2)`, so two lie in `U`; its three
top successors have successor weights `(1,1,2)`, so two lie in `V`.
By (7), each of those `U` predecessors has central good middles to
both `V` successors. Both paths through the `A` vertex are therefore
bad.

But a top translation's three-element fiber at this `A` output
contains one sharp `B` input and exactly two of its three top successors.
Exactly one top extension is bad, not two. This contradiction shows
that every `A` vertex has sharp degree two.

Its two top predecessors must now both lie in `V`, and its two top
successors both in `U`. No `A×A` endpoint pair has a top middle.
Every such pair must therefore have a sharp `B` middle.

For `b∈B`, write `\ell_b^-`, `\ell_b^+` for its sharp degrees;
both are in `{1,2,3}`. Counting the sharp edges and then the unique
middles just obtained gives

\[
 \sum_b\ell_b^- =\sum_b\ell_b^+=2f,
 \qquad \sum_b\ell_b^-\ell_b^+=f^2.
\]

For any `k,l∈{1,2,3}`, the elementary inequality
`(k−2)(l−2)≤1` says `kl≤2(k+l)−3`. Since `f+g=12`, summing gives

\[
 f^2\le8f-3g=11f-36.
\]

This is impossible: `f²−11f+36=(f−11/2)²+23/4>0`.
Thus `m=4,h=8` is excluded as well.

## The remaining four-central case has no sharp-degree-two vertex in `A`

At `m=4,h=9`, the central profile consists of four `(1,1)` vertices,
two `(1,2)` vertices `U_1,U_2`, two `(2,1)` vertices `V_1,V_2`,
and one `(2,2)` vertex `H`. Write `R` and `C` for the central
predecessor and successor pairs of `H`.

The unique central predecessors `u_1,u_2` of `U_1,U_2` are precisely
`Z\R`, because every central row has exactly one successor-weight-two
top vertex. Dually, the unique central successors `v_1,v_2` of
`V_1,V_2` are precisely `Z\C`.

Suppose `a∈A` has sharp degree two. Its top predecessor pair `P`
lies in `{H,V_1,V_2}`; the central predecessor pairs of these two
vertices partition `Z`. Its top successor pair `Q` similarly lies
in `{H,U_1,U_2}`, and their central successor pairs partition `Z`.

If both `P` and `Q` contain `H`, write their other elements as `V_j`
and `U_i`. Then `V_j` has central predecessor set `Z\R`, and
`U_i` has central successor set `Z\C`. Their central rectangles
both contain the pair `(u_i,v_j)`, contradicting unique goodness.

If `P` contains `H` but `Q` does not, then `Q={U_1,U_2}` and
their central successor pairs partition `Z`. The other element `V_j`
of `P` has predecessor set `Z\R={u_1,u_2}`. Its successor `v_j`
belongs to the successor pair of one `U_i`, again giving overlapping
central rectangles. The case where only `Q` contains `H` is dual.

Finally suppose neither pair contains `H`. Then `P={V_1,V_2}` and
`Q={U_1,U_2}`. A top translation's fiber at `a` has two sharp `B`
inputs and one top input. Thus exactly one of the two paths through
`a` from each element of `P` to `Q` is bad. A bad degree-four middle
has central replacement, by strict descent. The central-middle matrix
on `P×Q` is therefore a permutation matrix. Its entries here are
simply `1_{v_j=u_i}`. Hence `{v_1,v_2}={u_1,u_2}`, or `C=R`.
But then the path from `H` to itself has two central middles, again
impossible.

We conclude that every `A` vertex has sharp degree one. Thus `f≥g`,
and `f+g=11` gives `f≥6`. The top-input bound from the large-central
note is now `36+6f≤81`, giving `f≤7`. Only the two class-size
pairs stated above remain; they are not excluded here.
