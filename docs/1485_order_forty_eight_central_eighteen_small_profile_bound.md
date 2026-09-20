# Eighteen tops allow at most two small degree-five profiles

Proof, 20 September 2026. The local unused-top argument and the
reductions below have been independently audited. The final pure
central case uses the existing audited 200-fixture lemma; there is
no new enumeration or SAT premise, and no Lean theorem is claimed.

Assume order forty, minimum degree four, eight central elements,
and eighteen tops. Let `a` be the degree-five class size, and `q`
the number of its elements having three top predecessors and three
top successors. The others have profile size four.

**Theorem:** `q≤2`.

For a top use `P,C` for its central block sizes, `α` for its
degree-five successor count, and `γ` for its small-profile successor
count. In this setting all blocks have size at most three. The
[support capacities](1485_order_forty_eight_central_high_five.md)
and [singleton saturation theorem](1485_singleton_source_first_degree_saturation.md)
give

\[
 \alpha\le3,3,1\quad\text{when }C=1,2,3,
 \qquad0\le\gamma\le\alpha.
 \tag{1}
\]

We will use the central moments and profile incidence counts

\[
 \sum1=18,\quad\sum P=\sum C=32,\quad\sum PC=64,
 \quad\sum\alpha=4a-q,\quad\sum P\alpha=8a,
 \quad\sum_{P=3}\gamma=2q.
 \tag{2}
\]

The last equality holds because each three-profile has predecessor
block pattern `332`. In particular a `P=1` top has `γ=0`.
Subtracting twice the unweighted `α` identity from the weighted
one gives

\[
                \sum_{P=3}\alpha-\sum_{P=1}\alpha=2q.
 \tag{3}
\]

## 1. The unused-top identity removes two possible sources

The [unused-top upper bound](1485_first_degree_source_unused_tops.md#2-a-maximal-central-source-cannot-leave-no-unused-top)
with `r=4`, global block bound `M=3`, and `C=3` says
`18≤14+t` for any degree-five successor with profile size `t`.
Consequently

\[
                         C=3\quad\Longrightarrow\quad\gamma=0.
 \tag{4}
\]

Next suppose `C=2` and `α=3`. Apply the exact unused-top identity
to all three degree-five successors. Their good top-input sets have
total size `9−γ`, and the eight central-associated inputs are already
used. Thus the unused top set `W` has cardinality

\[
 |W|=18-8-(9-\gamma)=1+\gamma.
\]

If the three retained successor blocks are `C_(d_i)`, the same
identity gives

\[
 \sum_{w\in W}|C_w|=\sum_{i=1}^3|C_{d_i}|-8\le9-8=1.
\]

Every unused block is nonempty. Therefore `γ=0`. We have proved

\[
 C=2,\ \gamma>0\quad\Longrightarrow\quad
                    \gamma\le\alpha\le2.
 \tag{5}
\]

At equality `α=3` the three retained blocks are all triples and
there is exactly one unused singleton block. No assumption that the
retained tops are distinct was used.

## 2. The paired central moments give a short numerical bound

We may assume `q>0`. Write

\[
 u=n_{12},\quad v=n_{21},\quad z=n_{13},\quad w=n_{31},
 \quad t=n_{33},\qquad U=u+2z,\quad V=v+2w.
\]

Solving the four central moments in (2) gives

\[
\begin{aligned}
 n_{11}&=8+z+w-t,\\
 n_{32}&=4+U-2t,& n_{23}&=4+V-2t,\\
 n_{22}&=2-2U-2V+4t.
\end{aligned}
 \tag{6}
\]

The numbers of triple blocks in the two directions are

\[
 p=4+U+w-t\le4,\qquad c=4+V+z-t\le4,
 \tag{7}
\]

by the [one-hole theorem](1485_one_hole_first_output_grid.md).
In particular `t≥U+w` and `t≥V+z`.

Using (1), (4), and (5) on the `P=3` tops now gives

\[
\begin{aligned}
 2q=\sum_{P=3}\gamma
 &\le3w+2n_{32}\\
 &=8+2U+3w-4t\le8-2U-w.
\end{aligned}
 \tag{8}
\]

Dually `2q≤8−2V−z`. Thus `q≤4`.

## 3. Four small profiles force the excluded central grid

If `q=4`, equality in (8) and its dual forces
`U=V=w=z=t=0`. The only block types are

\[
                n_{11}=8,\quad n_{22}=2,\quad n_{23}=n_{32}=4.
 \tag{9}
\]

All four `32` tops have `γ=2`; by (5) they have `α=2`.
Equation (3) therefore gives `Σ_(P=1)α=0`: all eight unit tops
have `α=0`. The dual statement gives their `β=0` as well.

A central row of block pattern `3311` would have degree-five
successor count at most two, using (1) for its two triple blocks.
This is less than its required count `a≥q=4`. Thus no such row
occurs. The eight unit tops have eight singleton occurrences among
eight central rows. Since the only other patterns are `3221` and
`2222`, all rows have pattern `3221`. The dual argument applies to
columns.

Both triple-block counts equal four, so the one-hole theorem also
supplies the maximal-block intersection and deficiency conditions.
All hypotheses of the existing
[common finite central-profile lemma](1485_order_forty_eight_central_eighteen_two_small.md#common-finite-central-profile-lemma)
now hold. Its 200 exhaustive central fixtures admit no three-profile
at all, a contradiction. Hence `q≤3`.

## 4. Three small profiles are also impossible

Suppose `q=3`. The two versions of (8) imply
`2u+4z+w≤2` and `2v+4w+z≤2`. Hence `z=w=0` and
`u,v≤1`. Six small-profile incidences must fit among the `32`
tops, each contributing at most two, so `n32≥3`. The dual gives
`n23≥3`. Combining these facts with (6) and (7),

\[
        t\ge u,v,\qquad2t\le1+u,1+v.
\]

There are just two possibilities: `u=v=t=0` or `u=v=t=1`.
Also sharp-neighbor coverage gives `14−a≤a+3`, so `a≥6`.

In the second possibility the type counts are seven units, one
each of `12,21,33`, two `22`, and three each of `23,32`.
Each `32` top has `γ=2` and hence `α=2`. Put `e=α33≤1`.
By (3), `Σ_(P=1)α=e`. The remaining `P=2` tops must therefore
contribute

\[
 \sum_{P=2}\alpha=(4a-3)-(6+e)-e
                 =4a-9-2e\ge13.
\]

Their capacities instead give at most
`3+2·3+3·1=12`, a contradiction.

In the first possibility the inventory is (9). At least three of
the four `32` tops have positive `γ`, so have `α≤2`; the fourth
has `α≤3`. Thus `Σ_(P=3)α≤9`, and (3) gives a total `α≤3`
over all eight unit tops. A `3311` row would consequently have
total `α≤3+2=5<a`. As in §3, all central rows and columns must
have pattern `3221`, and the same common finite lemma excludes
the three-profile. This completes the proof of `q≤2`.

The argument is independent of the value of `a`, apart from the
displayed elementary class counts. Together with the separately
[proved exclusion at seven degree-five elements](1485_order_forty_eight_central_eighteen_seven_two_small.md),
it leaves at most one small profile when `a=7`.
