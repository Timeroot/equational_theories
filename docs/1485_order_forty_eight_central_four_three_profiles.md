# Sixteen tops and ten degree-five elements cannot have four three-profiles

Research analytic proof, 20 September 2026. The argument has been
independently audited. No SAT solver, finite graph enumeration, or Lean
theorem is used.

**Theorem.** An order-forty E1485 magma with minimum degree four,
eight central elements, sixteen tops, and ten degree-five elements
cannot have exactly four degree-five elements of top-profile size three.

Write `P,C` for the sizes of a top's central predecessor and successor
blocks, and `α,β` for its numbers of degree-five successors and
predecessors. Let `A_3` denote the four three-profile degree-five
elements; the remaining six have four-profile size.

## 1. Equality fixes all local degree-five incidences

The [new profile bound](1485_order_forty_eight_central_ten_five_profile_bound.md)
gives `4q+n22≤320−19h`. At `h=16,q=4`, its two sides can
agree only with `n22=0` and equality in every pointwise bound.
The resulting incidences are:

| Central type `(P,C)` | `(α,β)` |
| --- | --- |
| `(1,1)` | `(3,3)` |
| `(1,2)` | `(1,3)` |
| `(1,3)` | `(0,4)` |
| `(2,1)` | `(3,1)` |
| `(2,3)` | `(1,3)` |
| `(3,1)` | `(4,0)` |
| `(3,2)` | `(3,1)` |
| `(3,3)` | `(1,1)` |

Four entries use reciprocal balance to finish the equality information.
For example, at `(1,2)` equality first gives `α=1`, with
`β=3` or `4`. If `β=4`, reciprocal balance gives
`O−I=8−3β=−4`, while `I+P+β≤10` gives `I≤5`.
This contradicts `O≥3`. Thus `β=3`.
At `(3,2)`, equality gives `α=3` and `β∈{0,1}`. If
`β=0`, then `O−I=4`, whereas `O+C+α≤10` gives `O≤5`,
contradicting `I≥3`. The other two entries are dual.

Here `I,O` count the top predecessors and successors. We use the
standard reciprocal identity

\[
                     O-I=5(C-P)+3(\alpha-\beta).
\]

## 2. Central-row counting fixes the entire block-type inventory

Abbreviate

\[
 w=n_{11},\quad u=n_{12},\quad v=n_{21},\quad
 x=n_{13},\quad y=n_{31},\quad z=n_{33}.
\]

The central moments at sixteen tops give

\[
 x+y=w+z,\qquad n_{32}=w+u+x-y-z,
 \qquad4w+2(u+v)=16.                                  \tag{1}
\]

The last equation uses `n22=0`. Every central row contains four
tops, with `C` blocks summing to eight and `α` values summing to ten.
The table in §1 has the following consequences:

- A row of pattern `3311` contains two type-`(3,1)` tops and two
  tops of type `(2,3)` or `(3,3)`.
- A row of pattern `3221` contains two type-`(3,2)` tops. Its other
  two tops are either one `(1,3)` and one `(3,1)`, or one of types
  `(2,3),(3,3)` and one of types `(1,1),(2,1)`.
- A row of pattern `2222` contains three type-`(3,2)` tops and
  one type-`(1,2)` top.

Let `R_2222,R_3221` count the indicated central rows. Each top
occurs in exactly `P` central rows, so

\[
 R_{2222}=u,\qquad R_{3221}=x+w+2v,
 \qquad3n_{32}=3u+2R_{3221}.
\]

Substitute (1) into the last equation. It simplifies to

\[
                             x-y=2(z+v).
\]

The dual count gives `y−x=2(z+u)`. Nonnegativity forces
`u=v=z=0` and `x=y`. Equation (1) now gives the exact inventory

\[
 n_{11}=4,\qquad n_{13}=n_{31}=2,\qquad
 n_{23}=n_{32}=4,                                     \tag{2}
\]

with every other block type absent.

## 3. Three-profiles require four identical central blocks

A type-`(3,1)` top has `(α,β)=(4,0)`. Reciprocal balance and
the ordinary degree bounds force `I=3,O=5`. It therefore has no
ordinary `B` successor, since `10−C−α−O=0`.

Let `γ` count its successors in `A_3`. In its multiplication row,
the sixteen top inputs have four central outputs and `3α−γ`
degree-five outputs: each four-profile output uses three top inputs,
and each three-profile output uses two. There are no `B` outputs.
There are no top outputs either, by
[small-block confinement](1485_top_return_small_blocks.md), since the
first input has `P=3`. Thus

\[
                            16=4+12-\gamma,
\]

so `γ=0`: type `(3,1)` supplies no predecessor to `A_3`.

Each three-profile has two predecessor `P` blocks of size three and
one of size two. By (2) and the preceding paragraph, its two triple
blocks come from type-`(3,2)` tops and its double block from a
type-`(2,3)` top. There are four tops of the latter type and each has
`α=1`; the four elements of `A_3` each require one such predecessor.
Consequently every type-`(2,3)` top supplies one of these double blocks.

By §2 and `n12=0`, each central row contains either zero or two
type-`(3,2)` tops. Their four `P` blocks have total size twelve,
so their union is a fixed set `Z_0` of exactly six central labels.
In any three-profile, the two selected triple blocks are disjoint and
therefore cover all of `Z_0`. Its double block must be the fixed
complement `R=Z\setminus Z_0`.

It follows that all four type-`(2,3)` tops have `P` block exactly
`R`. Any central label in the nonempty set `R` then has those four
tops as its entire central row. Their `α` values sum to four,
contradicting the required sum ten. This excludes the equality case.

Combining this theorem with the preceding profile bound reduces the
sixteen-top, ten-degree-five branch to `q≤3`. It does not exclude
those lower-profile cases or the separate fifteen-top branch.
