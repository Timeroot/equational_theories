# Fifteen tops and six small profiles: an intermediate incidence table

Independently audited analytic necessary-condition lemma, 20 September
2026. This is a historical necessary refinement, **not itself an
exclusion**. The configuration is now excluded analytically by the
[unused-top source argument](1485_first_degree_source_unused_tops.md#3-fifteen-tops-and-eight-central-elements).
No enumeration or SAT premise is used in this note.

The subsequent [unused-top source bound](1485_first_degree_source_unused_tops.md#3-fifteen-tops-and-eight-central-elements)
excludes this entire ten-degree-five configuration analytically. The
reduction below is retained as independent intermediate reasoning,
not as a currently open case or a dependency of that exclusion.

Assume order forty, minimum degree four, eight central elements,
fifteen tops, and ten degree-five elements, six of which have three
top predecessors and successors. The other four have four. For a top,
write `P,C` for the central block sizes and `α,β` for its degree-five
successor and predecessor counts.

**Theorem.** The complete central block inventory and all incidences
outside type `22` are

| `(P,C)` | Number | `(α,β)` |
| --- | ---: | --- |
| `13` | 2 | `(1,4)` |
| `31` | 2 | `(4,1)` |
| `23` | 2 | `(1,3)` |
| `32` | 2 | `(3,1)` |
| `22` | 7 | `1≤α,β≤3` |

There are no other types. On the seven `22` tops,

\[
                           \sum\alpha=\sum\beta=16.    \tag{1}
\]

Every residual ordered top pair—one whose output is neither central
nor degree five—has first input with `P≥2` and second input with
`C≥2`. There are exactly thirteen residual pairs, and their first-input
`P` weights, or equivalently their second-input `C` weights, sum to 32.

## 1. The block inventory follows from the one-hole bound

The [one-hole theorem](1485_one_hole_first_output_grid.md) gives at most
four triple blocks in each direction. At fifteen tops the singleton
count is two less than the triple count in either direction, so there
are at most two singleton blocks in each direction. The mixed moment is

\[
        n_{11}+n_{33}-n_{13}-n_{31}
        =\sum(P-2)(C-2)=-4.
\]

Since `n13,n31≤2`, this forces

\[
 n_{13}=n_{31}=2,\quad n_{11}=n_{33}=0,
 \quad n_{12}=n_{21}=0,
 \quad n_{23}=n_{32}=2,
 \quad n_{22}=7.                                      \tag{2}
\]

This inventory argument requires only fifteen tops and the existence
of a three-profile, not the particular degree-five class size.

## 2. Four units of local slack fix all non-double incidences

Use the [nonnegative local slack](1485_order_forty_eight_central_ten_five_profile_bound.md#2-a-pointwise-inequality-summed-over-all-tops)

\[
 D=-3PC+8(P+C)-19-(P-2)\alpha-(C-2)\beta
                            -\mathbf1_{P=C=2}.
\]

Here the exact sum is

\[
                  \sum D=320-19\cdot15-4\cdot6-7=4.    \tag{3}
\]

The local incidence intervals are `α∈{3,4},{1,2,3},{0,1}`
according as `C=1,2,3`, and the dual intervals hold for `β`.
For the types in (2), the slacks are

| Type | `D` |
| --- | --- |
| `13` | `4+α−β` |
| `31` | `4+β−α` |
| `23` | `3−β` |
| `32` | `3−α` |
| `22` | `0` |

No `31` top can have zero slack. Such a top would have
`(α,β)=(4,0)`. Reciprocal balance and the ordinary degree bounds
give `I=3,O=5`, and hence no ordinary degree-eight successor.
The [small-block return theorem](1485_top_return_small_blocks.md)
forbids a top-valued top product with its first input, since `P=3`.
If `γ` counts its three-profile degree-five successors, its row of
fifteen top inputs would therefore give

\[
                          15=4+3\cdot4-\gamma,
\]

so `γ=1`. This top would have three four-profile successors.

However, the only singleton-predecessor tops are the two `13`
tops, each with `α≤1`. Their successors are all four-profile:
a three-part partition of eight by blocks of size at most three
has no singleton part. Every four-part partition of eight by such
blocks has equally many singleton and triple parts. Thus the total
number of four-profile incidences at `P=3` tops equals that at
`P=1` tops, and is at most two. This contradicts the three
incidences just obtained. The dual proof rules out zero slack at
type `13`.

The four `13,31` tops consequently each contribute at least one
to (3). They each have slack exactly one; every other top has
zero slack. Hence the possibilities are

\[
\begin{array}{c|c}
13&(\alpha,\beta)=(0,3)\text{ or }(1,4)\\
31&(\alpha,\beta)=(3,0)\text{ or }(4,1)\\
23&(\alpha,\beta)=(1,3)\\
32&(\alpha,\beta)=(3,1).
\end{array}                                            \tag{4}
\]

For `23`, zero slack first gives `β=3`; `α=0` would force
`O−I=-4` and `I≤5`, contrary to `O≥3`. The `32` check is dual.

Let `k` count the `13` tops of type `(1,4)`, and `l` the `31`
tops of type `(4,1)`. The exact incidence identity

\[
 \sum(P-2)\alpha=2q=12
\]

reads `(12+l)−k=12`, so `l=k∈{0,1,2}`. Since
`Σα=Σβ=34`, the seven double-double tops have total
`α=β=20−2k`.

## 3. Residual top-input fibers force `k=2`

For a top `u`, let `γ_u` count its three-profile successors and
let `R_u` count its residual top inputs, whose products lie outside
the central and degree-five classes. The exact fiber count is

\[
                       R_u=15-4C_u-3\alpha_u+\gamma_u. \tag{5}
\]

Central outputs use four top inputs each; degree-five outputs use
two or three according to profile size. Summing (5) gives

\[
 \sum R_u=13,\qquad\sum P_uR_u=32.                   \tag{6}
\]

For completeness, the weighted sum is
`15·32−4·64−3·80+6·8=32`, since every three-profile's
predecessor blocks partition the eight central elements.

At a singleton-predecessor top, `γ=0,C=3`, so `R=3−3α`.
Therefore

\[
 \sum_{P=1}R=6-3k,
 \qquad
 \sum_{P=2}R=3\sum R-\sum PR-2\sum_{P=1}R=6k-5.      \tag{7}
\]

At a `22` top, (5) is `R=7−3α+γ`, with `1≤α≤3`.
This always gives `R≥3−α`: use `γ≥0` for `α=1,2`,
and nonnegativity of `R` for `α=3`. Consequently

\[
 6k-5=\sum_{P=2}R
      \ge\sum_{22}R
      \ge\sum_{22}(3-\alpha)=1+2k.
\]

Thus `k≥2`, hence `k=l=2`. Equations (4) give the asserted
incidence table, and `20−2k=16` proves (1).
Equation (7) now gives zero residual pairs with `P=1` first input;
the dual calculation excludes `C=1` second inputs. The counts in
(6) remain valid. These are necessary restrictions, not a construction
or an exclusion of the remaining fifteen-top branch.
