# Sixteen tops with one small profile: the remaining incidence table

Independently audited analytic necessary-condition lemma, 20 September
2026. This does **not** exclude the configuration or construct a
model. No finite search or SAT premise is used.

Assume order forty, minimum degree four, eight central elements,
sixteen tops, and ten degree-five elements, exactly one of which has
three top predecessors and successors. Call that element `a₀`.
The other nine degree-five elements have four-profile size.

For a top write `P,C` for its central predecessor and successor block
sizes, `α,β` for its degree-five successor and predecessor counts,
and `γ,δ∈{0,1}` for whether it precedes or succeeds `a₀`.

**Theorem.** Every central row and column has block-size pattern
`3221`. The complete top incidence inventory is

| `(P,C)` | Number | `(α,β)` |
| --- | ---: | --- |
| `11` | 1 | `(4,4)` |
| `12` | 2 | `(2,4)` |
| `13` | 1 | `(1,4)` |
| `21` | 2 | `(4,2)` |
| `22` | 1 | `(3,3)` |
| `22` | 3 | `(2,2)` |
| `23` | 2 | `(1,3)` |
| `31` | 1 | `(4,1)` |
| `32` | 2 | `(3,1)` |
| `33` | 1 | `(1,1)` |

The three top predecessors of `a₀` are the two `32` tops and the
unique `22:(3,3)` top. Its three top successors are the two `23`
tops and that same `22:(3,3)` top.

## 1. A central row cannot have four double blocks

The [existing incidence bounds](1485_order_forty_eight_central_ten_five_profile_bound.md#1-the-local-incidence-intervals)
give `1≤P,C≤3` and `α≤f(C),β≤f(P)`, with `f=(4,3,1)`.
Every central row has four `C` blocks partitioning eight labels,
its `α` values sum to ten, and its `γ` values sum to one.

The residual top-input count in a row is

\[
                        R=16-4C-3\alpha+\gamma\ge0.    \tag{1}
\]

Thus any `C=2,α=3` top has `γ=1`. A `2222` central row
with `α` sum ten needs at least two such tops, contradicting its
`γ` sum one. Consequently every central row is `3311` or `3221`.

A `3311` row can reach `α` sum ten only with both singleton
blocks having `α=4` and both triple blocks having `α=1`.
In a `3221` row, the two double tops cannot both have `α=3`,
since then its `γ` sum would be at least two. Its `α` sum
therefore forces the pattern

\[
               C=1:\alpha=4,\quad C=3:\alpha=1,
               \quad C=2:\alpha=3,2.
\]

Since every top occurs in a central row, these values apply globally:
all `C=1` tops have `α=4`, all `C=3` tops have `α=1`, and
every `C=2` top has `α=2` or `3`. The dual statements hold
for `P` and `β`.

## 2. Every row and column is in fact `3221`

Put `v=7−2C−α`. The preceding values show `v∈{0,1}`:
it equals one at every `C=1` top and at every `C=2,α=2` top.
The exact incidence sum gives

\[
                   \sum v=7\cdot16-2\cdot32-39=9.
\]

Let `c` count triple successor blocks. There are also `c` singleton
successor blocks, since sixteen blocks have total size 32.
The number of double blocks is `16−2c`, of which `9−c` have
`α=2`. Thus exactly `7−c` tops have `C=2,α=3`.

Each of these has `γ=1` by (1), and there are only three top
predecessors of `a₀`. The [one-hole bound](1485_one_hole_first_output_grid.md)
gives `c≤4`. Hence `7−c≤3` forces `c=4`, with exactly
three `C=2,α=3` tops. They are all the predecessors of `a₀`.

Every central row has `γ` sum one and consequently contains one
of these double-block tops. It cannot be `3311`; all rows are `3221`.
Dually, there are four triple predecessor blocks, every central
column is `3221`, and all successors of `a₀` have `P=2,β=3`.

## 3. The moments fix the corner counts

Let `n_ij` count block types. Since each central row contains exactly
one singleton successor block, the `P` blocks indexed by `C=1` tops
partition the eight central labels. There are four such tops, so
their number with `P=1` equals their number with `P=3`:

\[
                             n_{11}=n_{31}.
\]

Dually `n11=n13`. The mixed moment
`n11+n33=n13+n31` then gives `n33=n11`. Put this common
corner count equal to `x`. The remaining margins yield

\[
 n_{12}=n_{21}=n_{23}=n_{32}=4-2x,
 \qquad n_{22}=4x.                                   \tag{2}
\]

The predecessor partition of `a₀` is `332`, and all its tops
have `C=2,α=3`. Thus it contains two `32` tops and one `22`
top. The former condition gives `x≤1`, and the latter gives `x≥1`.
Hence `x=1`, proving all block counts in the table.

There are exactly three `C=2,α=3` tops: the two `32` tops and
one `22` top. All other double-successor tops have `α=2`.
Dually the two `23` tops and one `22` top have `β=3`, and all
other double-predecessor tops have `β=2`.

At type `22`, `α=3,β=2` is impossible: reciprocal balance gives
`O−I=3` while `O≤10−C−α=5` and `I≥3`. The dual pair
`α=2,β=3` is likewise impossible. Therefore the two distinguished
`22` tops are the same top, with `(α,β)=(3,3)`; the other three
have `(2,2)`. The incidences of all other types were already fixed
in §1. This proves the claimed necessary table and profile descriptions.

The remaining question is whether this incidence system, together with
the full E1485 multiplication constraints, is impossible. No answer to
that question is asserted here.
