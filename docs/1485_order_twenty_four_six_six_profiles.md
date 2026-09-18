# Order twenty-four: excluding the six/six case by profile rigidity

Research note, 18 September 2026. This analytically excludes the
six/six three-central incidence case.
Use the [three-central incidence reduction](1485_order_twenty_four_three_central_reduction.md).
Write `Z,A,B,T` for the degree classes `3,4,6,8`, and assume

\[
 (|Z|,|A|,|B|,|T|)=(3,6,6,9). \tag{1}
\]

Every intermediate vertex has three top neighbors in each direction.
Each `A` and each `B` has one sharp neighbor in either direction.
Thus each `B` additionally has two ordinary `B` predecessors and
successors. Each top vertex has one central, two `A`, two `B`, and
three top neighbors in each direction.

The top grid has four parallel classes of lines: central rows and
columns, and the two opposite-parity transversal classes `P_0,P_1,P_2`
and `Q_0,Q_1,Q_2`. An `A` predecessor set is a `P` line and an `A`
successor set a `Q` line. Each line of either class occurs twice.
Each pair of profiles occurs at most once, so the six `A` profiles
are the complement of a permutation in the `3×3` profile grid.

## Possible B lines

Fix `b∈B`. Only two `A×{b}` endpoint pairs can have a `B` middle:
the unique sharp successors of their `A` endpoints must be the two
`B` predecessors of `b`. Every other such endpoint pair has only top
middles and hence exactly one. If `TopPred(b)` did not meet some
`Q_q` once, both `A` vertices with that successor profile would have
to be among those two exceptions. Hence at least two of the `Q`
intersection counts are one. Their sum is three, so the third is
one as well.

The set `TopPred(b)` also meets every central row once. In the affine
plane of order three, a three-point set transversal to two parallel
classes is a line in one of the other two classes. Explicitly, label
the two given coordinates by `F_3`: its graph is a permutation of
three points, and every such permutation is affine. Therefore

\[
 \operatorname{TopPred}(b)\text{ is a }P\text{ line or central column}.
 \tag{2}
\]

Dually, its top successor set is a `Q` line or central row. Call the
central-column and central-row possibilities *degenerate*. Any line
of a predecessor type meets any line of a successor type once.
Consequently every pair of intermediate endpoints has exactly one
ordinary top middle.

At this point the six predecessor lines cover each top point twice.
If `a_p` is the multiplicity of `P_p` and `b_c` the multiplicity of
central column `c`, this says `a_p+b_c=2` for all `p,c`. Thus each
orientation has constant multiplicity: zero, one, or two copies of
each of its three lines. There are three choices in each direction,
but the next argument excludes every degenerate choice.

## A uniform-fiber formula

Let `g(b)` be the number of good two-paths `t→b→v` with both
endpoints top. Label `A={a_i}` and `B={b_i}` so that `a_i⇒b_i`,
and put `TopPred(a_i)=P_{p_i}`.

For each `t∈TopPred(b)`, the fiber `L_t^{-1}(b)` has size three.
It contains the unique sharp `A` successor of `b`. Its other inputs
are among the two `B` successors of `b` and its three top successors.
If `b→b_j`, the path `t→b→b_j` has a smaller ordinary middle exactly
when `t∈P_{p_j}`: that smaller middle must be the unique sharp
predecessor `a_j` of `b_j`. There is no central middle, and no other
degree below six can occur. Strict minimum-good-middle uniqueness
therefore gives

\[
 t*b_j=b\quad\Longleftrightarrow\quad t\notin P_{p_j}
 \qquad(t\in\operatorname{TopPred}(b),\ b\to b_j).
 \tag{3}
\]

Summing the three size-three fibers and subtracting their three
sharp `A` inputs yields

\[
 \begin{aligned}
 g(b)
 &=6-\sum_{b\to b_j\in B}
       \bigl(3-|\operatorname{TopPred}(b)\cap P_{p_j}|\bigr)\\
 &=\sum_{b\to b_j\in B}
       |\operatorname{TopPred}(b)\cap P_{p_j}|.
 \end{aligned} \tag{4}
\]

There are exactly two terms. If the predecessor profile is degenerate,
each intersection has size one, so `g(b)=2`. If it is a `P` line,
each intersection has size zero or three, so `3` divides `g(b)`.
The entirely dual fiber count gives

\[
 \begin{array}{c|cc}
 &\text{nondegenerate}&\text{degenerate}\\ \hline
 \text{predecessor profile}&3\mid g(b)&g(b)=2\\
 \text{successor profile}&3\mid g(b)&g(b)=2.
 \end{array} \tag{5}
\]

Thus exactly one of the two profiles cannot be degenerate.

## Two degenerate profiles are also impossible

Suppose `TopPred(b)` is a central column and `TopSucc(b)` a central
row. The central-successor label of every predecessor endpoint is
constant, as is the central-predecessor label of every successor
endpoint. If those labels agree, all nine endpoint pairs have a
central middle; therefore `g(b)=0`, contrary to (5).

If the labels differ, none of the nine pairs has a central middle.
As the predecessor endpoint varies along a central column, its `P`
profile runs through all three values. As the successor varies along
a central row, its `Q` profile does likewise. The six occupied `A`
profile pairs give six smaller `A` middles. The three remaining pairs
have no smaller ordinary middle, so their paths through `b` are good
by strict minimum-good-middle uniqueness. Hence `g(b)=3`, again
contrary to (5).

We conclude that every `B` top predecessor profile is a `P` line and
every `B` top successor profile a `Q` line. In particular the nine
orientation combinations have reduced to a single one.

## A degree-six fiber gives the final contradiction

Fix an ordinary `B` edge `b_i→b_j`. Let `a` be the unique sharp
`A` successor of `b_i`. Suppose that `TopSucc(a)` and `TopSucc(b_j)`
are different. Both are `Q` lines, hence they are disjoint.

For each of the three `v∈TopSucc(b_j)`, the path `b_i→b_j→v`
has no smaller ordinary middle. Indeed, the only `A` successor of
`b_i` is `a`, and `v` is not a successor of `a`; a central middle
is impossible because `b_i` has no central successor. Strict descent
therefore makes all three paths good. Consequently
`L_{b_i}^{-1}(b_j)` contains all three of these top inputs. It also
contains the unique sharp `A` successor of `b_j`, since the latter
edge makes the corresponding two-path good. These are four distinct
inputs, the entire fiber size `24/6=4`.

But `b_j` has two `B` successors. At most one is the unique sharp
`B` successor of `a`. Choose another, say `b_k`. The path
`b_i→b_j→b_k` then has no `A` middle: its only candidate is `a`.
It has no central middle either, so strict descent makes it good.
The additional input `b_k` lies in `L_{b_i}^{-1}(b_j)`, contradicting
the size-four fiber. Thus every ordinary `B` edge satisfies

\[
 b_i\to b_j\quad\Longrightarrow\quad
 \operatorname{TopSucc}(\text{sharp }A\text{ successor of }b_i)
 =\operatorname{TopSucc}(b_j). \tag{6}
\]

For completeness, the dual version of (4) is

\[
 g(b)=\sum_{b_i\to b\text{ in }B}
 \left|\operatorname{TopSucc}(b)\cap
 \operatorname{TopSucc}(\text{sharp }A\text{ successor of }b_i)\right|.
 \tag{7}
\]

There are two terms. Equation (6) makes each term three, so `g(b)=6`
for every `b∈B`. But the 81 top endpoint pairs include 27 with a
central good middle.
Each of the six `A` vertices has six good top-endpoint paths, by its
three top fibers with two top inputs each, accounting for another 36
pairs. Only 18 pairs remain, whereas `g(b)=6` for six `B` vertices
would require 36 more.

This excludes (1). Together with the
[nine/three exclusion](1485_order_twenty_four_three_central.md) and
the [base reduction](1485_order_twenty_four_three_central_reduction.md),
it excludes every order-24, minimum-degree-three model having exactly
three central vertices.

## Optional profile and matrix consequences

These observations were obtained before the final fiber argument;
they are not needed for the exclusion above.

Relabel the profile indices so that the missing `A` profiles are
`(p,p)`. Write a `B` profile as `(r_b,s_b)`. If `r_b≠s_b`, its
entire top endpoint rectangle has a smaller `A` middle, and `g(b)=0`.
If `r_b=s_b`, it has no `A` middle; exactly three of the nine pairs
have a central middle. Thus `g(b)=6`. There is at most one `B`
vertex at each diagonal profile, since two would give two equal-degree
minimum middles at those six remaining pairs. Call these at most
three diagonal-profile vertices active. The proof above forces all
six `B` vertices active, giving an alternative final contradiction.

Formula (4) says that for an active `b`, both `B` successors `b_j`
satisfy `p_j=r_b`; for an inactive `b`, both satisfy `p_j≠r_b`.
There is a dual restriction on predecessors. Both `B` profile
marginals are two, so its six profile pairs form a `3×3` nonnegative
matrix with all row and column sums two and diagonal entries at most one.

Let `P` be top adjacency from the twelve intermediate vertices to `T`,
and `Q` the reverse adjacency. The unique ordinary top middle for
every pair of intermediate endpoints gives

\[
 PQ=J_{12},\qquad (QP)^2=16J_9. \tag{8}
\]

The second identity also uses that every top vertex has four
intermediate predecessors and successors. These identities by
themselves did not provide a rank contradiction.
