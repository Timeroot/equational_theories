# Eighteen tops cannot have eight degree-five elements with one small profile

Independently audited proof, 20 September 2026. This excludes the order-forty case
`m=8,h=18,a=8,q=1`. The new reduction is analytic; its final central
profile is exactly the one excluded by the already audited 200-fixture
check for the two-small-profile case. No new enumeration or SAT premise
is used. This is not a Lean theorem or an exclusion of every
eighteen-top branch.

## 1. Unit weighted defect

For a top let `P,C` be its central predecessor and successor block
sizes, `α,β` its successor and predecessor counts in the degree-five
class, and define

\[
                  v^+=7-2C-\alpha,\qquad
                  v^-=7-2P-\beta.
\]

The support bounds make these nonnegative. Also `v^+≥1` when
`C=1`, and `v^-≥1` when `P=1`. The
[weighted central identity](1485_order_forty_eight_central_top_bound.md)
and its dual give

\[
                  \sum(P-1)v^+=\sum(C-1)v^-=1.          \tag{1}
\]

Write `n_pc` for the paired central block counts. A type `(3,1)`
would already contribute at least two to the first sum, and a type
`(1,3)` at least two to the second. Hence both are absent. Put

\[
                  u=n_{12}\le1,\qquad v=n_{21}\le1,
                  \qquad t=n_{33}.
\]

The moments `Σ1=18,ΣP=ΣC=32,ΣPC=64` give

\[
\begin{aligned}
n_{11}&=8-t,\\
n_{32}&=4+u-2t,&n_{23}&=4+v-2t,\\
n_{22}&=2-2u-2v+4t.
\end{aligned}                                          \tag{2}
\]

In particular the predecessor and successor triple counts are
`4+u−t` and `4+v−t`. Since there is a three-element first-output
profile, the [one-hole bound](1485_one_hole_first_output_grid.md)
makes each count at most four. Therefore

\[
                             t\ge u,\qquad t\ge v.     \tag{3}
\]

## 2. A mixed singleton block cannot occur

Suppose `v=n21=1`, and call that top `s`. Its contribution to
the first sum in (1) is at least one, so it consumes the entire
sum. Thus

\[
            \alpha_s=4,
\]

and every other top with `P>1` has `v^+=0`. In particular,
all such tops with `C=2` have `α=3`, and those with `C=3`
have `α=1`.

The only possible exception among the `C=2` tops is a type
`(1,2)` top, of which there is at most one. If it exists, it
consumes the dual sum in (1), giving `β=4`. Let `I,O` be its
top predecessor and successor counts. Central shadows give `O≥3`,
and the ordinary degree bound gives `I≤10−P−β=5`. Reciprocal
balance says

\[
                   O-I=5(C-P)+3(\alpha-\beta)=3\alpha-7.
\]

Thus `α≤1` is impossible, and this exceptional top has `α≥2`.

A central row of type `2222` would consequently have `α` sum
at least eleven, not eight. Such rows do not occur. A `3221`
row containing `s` would have `α` sum at least

\[
                        4+1+3+2=10,
\]

again impossible. Hence every row containing `s` must have type
`3311`. Since `P_s` has two elements, there must be at least two
such rows.

On the other hand, the total occurrences of singleton successor
blocks in central rows are

\[
                     n_{11}+2n_{21}=10-t.
\]

There are eight central rows and none is `2222`. If `R` of them
are `3311`, their singleton occurrences total `8+R`. Thus
`R=2−t`. But (3) gives `t≥1`, so `R≤1`, a contradiction.
We conclude `v=0`. Applying the same argument to the opposite magma
gives `u=0` as well.

## 3. The same central profile as the two-small case

Now no singleton block is paired with a nonsingleton block. A
little more can be said about the unique defect in (1). It is
supported on exactly one `P=2` top. That top cannot have `C=3`:
it would have `α=0`, while the dual identity forces `β=3`.
Reciprocal balance would give `O-I=-4`, and `I≤5` would imply
`O≤1`, contrary to the central-shadow bound. Thus the unique
successor defect is at a type-`(2,2)` top with `α=2`.
Dually the unique predecessor defect is at a type-`(2,2)` top
with `β=2`.

They must be the **same** top. Otherwise the first would have
`(α,β)=(2,3)`, giving `O-I=-3` and `I≤5`, hence `O≤2`.
Therefore exactly one type-`(2,2)` top has `(α,β)=(2,2)`;
all other such tops have `(3,3)`.

In particular every `C=2` top has `α=3`, apart from this one
with `α=2`.
Consequently a `2222` row would again have `α` sum at least
eleven, and is impossible.

The singleton successor occurrences now total `n11=8−t`. Since
every central row is `3311` or `3221`, this same total is `8+R`
for a nonnegative number `R`. Thus `t=R=0`. Substituting into
(2) gives

\[
                   n11=8,\quad n22=2,
                   \quad n23=n32=4,\quad n33=0,         \tag{4}
\]

and every central row and column has pattern `3221`.

This is precisely the central profile used in
[the common finite central-profile lemma](1485_order_forty_eight_central_eighteen_two_small.md#common-finite-central-profile-lemma).
That finite graph lemma does not encode `α,β` or the number two
of small profiles. Its hypotheses are (4), the central incidence
axioms, and the necessary one-hole consequences of the existence of
**one** small profile. It exhaustively constructs the same 200
central fixtures and shows that none admits even one compatible
three-element first-output profile.

Here `q=1` supplies that existence assumption, so the identical
finite lemma applies without modifying its checker or generating new
cases. This contradiction completes the exclusion.

The weighted bound already gives `q≤2` when `h=18,a=8`. Combining
the present result with the two-small-profile exclusion shows that any
remaining case with these class sizes must have `q=0`: all its
degree-five profiles have size four. That remaining case is not
excluded by this note.
