# Eighteen tops and seven degree-five elements have at most two small profiles

Independently audited proof, 20 September 2026. Assume order
forty, minimum degree four, eight central elements, eighteen tops,
and seven degree-five elements. Let `q` count the latter's
three-element top profiles; the other profiles have size four.
Then

\[
                              \boxed{q\le2.}
\]

The reduction is analytic and its last subcase uses the already
audited 200-fixture three-profile lemma; there is no new enumeration
or SAT premise. This does not exclude `q=0,1,2` or the whole
eight-central branch. It assumes no balanced degree-eight counts
and is not yet a Lean theorem.

## 1. A small weighted budget forces distinct singleton labels

Use the usual top central block sizes `P,C`, degree-five neighbor
counts `α,β`, and deficits

\[
                 v^+=7-2C-\alpha,\qquad v^-=7-2P-\beta.
\]

They are nonnegative by the support bounds. The
[weighted central identities](1485_order_forty_eight_central_top_bound.md)
give

\[
           \sum(P-1)v^+=\sum(C-1)v^-=E:=6-q\ge0.       \tag{1}
\]

Every central row has `v^+` sum `12−7=5`, and every column
has `v^-` sum five. The
[singleton-source saturation theorem](1485_singleton_source_first_degree_saturation.md)
gives `α≤3` at `C=1`, and `β≤3` at `P=1`, since
`18>4²`. Hence

\[
             C=1\Longrightarrow v^+\ge2,
             \qquad P=1\Longrightarrow v^-\ge2.       \tag{2}
\]

Suppose for contradiction `q≥3`. Equation (1) gives `0≤E≤3`.
A central row without a singleton-`P` top would have deficit at
most the weighted sum `E`, since every top in that row has
`P−1≥1`. This contradicts its required sum five. Every label
therefore supports a singleton `P` block; the dual statement holds
for singleton `C` blocks.

There is a size-three first-output profile, so the
[one-hole bound](1485_one_hole_first_output_grid.md) makes both
triple-block counts at most four. The singleton margins are four
plus the triple counts. To cover eight labels they must therefore
be exactly eight, with all labels distinct, and there are exactly
four triple blocks in each direction.

In a central row its unique singleton-`P` top supplies deficit
at least `5−E≥2`, since all nonsingleton contributions together
are at most (1). A type `(1,3)` top has `v^+≤1`, so cannot
occur. Dually there is no `(3,1)` top.

## 2. A single mixed pair would force overlapping rectangles

Write `n_pc` for paired central type counts. The moments
`Σ1=18,ΣP=ΣC=32,ΣPC=64`, with four triples in each direction
and no `(1,3)` or `(3,1)`, give

\[
 n12=n21=n33=u,\quad n11=8-u,\quad n22=2,
 \qquad n23=n32=4-u.
\]

Each type `(2,1)` contributes at least two to the first sum in
(1), so `2u≤E≤3`. Thus `u` is zero or one.

If `u=1`, let `s` be the unique `(1,2)` top and `t` the
unique `(2,1)` top, with `P_s={r}` and `C_t={c}`.
The row at `r` contains no other singleton-`P` top, and
`v_s^+≤3`, so it needs at least two units from nonsingletons.
The top `t` contributes at least two to the global weighted sum;
all other tops together contribute at most `E−2≤1`. It follows
that the row must contain `t`, so `r∈P_t`.

Dually, the column at `c` has no other singleton-`C` top and
`v_t^-≤3`. The unique `(1,2)` top uses at least two of the
dual weighted budget, and all other contributions total at most
one. Thus this column contains `s`, giving `c∈C_s`.
The central rectangles of `s,t` overlap at `(r,c)`, impossible.

Therefore `u=0`. The central type counts are precisely

\[
                     n11=8,\quad n22=2,
                     \quad n23=n32=4.                \tag{3}
\]

The eight unit rectangles have distinct predecessor and successor
labels, so every central row and column is `3221`. Simultaneous
equality in the one-hole triple bound gives the complete maximal-block
intersection matrix and the disjoint deficiency supports. Hence all
hypotheses of the
[common 200-fixture central-profile lemma](1485_order_forty_eight_central_eighteen_two_small.md#common-finite-central-profile-lemma)
hold. That lemma says that no such central system admits even one
three-element first-output profile. Here there are `q≥3`, a final
contradiction. This proves `q≤2`.
