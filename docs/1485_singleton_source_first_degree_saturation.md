# Saturating the first-degree successors of a singleton central source

Independently audited analytic lemma, 20 September 2026. This
uses only finite E1485 central incidence and the first-output profile
theorem. No search, SAT result, or balance assumption at other degree
classes is used. It is not yet formalized in Lean.

Let the minimum translation degree be `r≥2`, let `Z` be the
central class, and let `T` be the top class, with `h=|T|`.
Suppose the first noncentral top-output degree is `r+1`. Write
`A` for that degree class. For a top `u`, put

\[
           P_u=Col(u)\cap Z,\qquad C_u=Row(u)\cap Z.
\]

**Theorem.** If `C_u` is a singleton, then `u` has at most
`r` successors in `A`. If it has exactly `r`, writing `t_a`
for the top-profile size of each of those successors gives

\[
                  \boxed{h=r+\sum_{a\in Row(u)\cap A}(t_a-1)
                         \le r^2.}                    \tag{1}
\]

In particular `h>r²` forces at most `r−1` such successors.
The dual result bounds first-degree predecessors when `P_u` is
a singleton.

## Proof

Write `C_u={c}` and `R=Row(c)`. The set `R` consists of
`r` tops, and their `C` blocks partition `Z`. For any successor
`a∈A` of `u`, let `U_a,V_a` be its top predecessor and
successor profiles. The
[first-output profile theorem](1485_first_successor_degree_profiles.md)
gives

\[
 u\in U_a,\quad |U_a|=|V_a|=t_a\le r,
 \quad (|C_x\cap P_y|)_{x\in U_a,y\in V_a}
       \text{ is a permutation matrix}.
\]

Its row at `u` says that exactly one member `d_a∈V_a` has
`c∈P_(d_a)`, or equivalently belongs to `R`. Put

\[
                         G_a=V_a\setminus\{d_a\}.
\]

The sets `G_a` consist precisely of the top inputs `v` for which
`u*v=a`: the good top-product graph at the first output is the
complement of the central permutation matrix. Consequently the
`G_a` are pairwise disjoint as `a` varies and are contained in
`T\R`. Since the `C` blocks on `V_a` partition `Z`, those
on `G_a` partition `Z\C_(d_a)`.

Suppose first that at least `r` successors are available, and
select any `r` distinct ones. For each `d∈R`, let `m_d` be
the number of selected successors retaining `d_a=d`. Thus
`Σ_(d∈R)m_d=r`.

For a label `z∈C_d`, the total multiplicity of `z` in the
`C` blocks of all selected good sets is exactly `r−m_d`.
Globally every label has `C`-block valency `r`; the partition
on `R` accounts for one, leaving valency `r−1` on `T\R`.
The selected good sets are disjoint subsets of `T\R`, so

\[
                         r-m_d\le r-1.
\]

Every `C_d` is nonempty, hence this proves `m_d≥1` for each
of the `r` elements `d∈R`. Their sum is `r`, so all equal
one. The selected good sets therefore exhaust the full `C`-block
valency of `T\R` at every label. Any unused top has a nonempty
`C` block, so there are no unused tops:

\[
                    T\setminus R=\bigsqcup_a G_a.
\]

Taking cardinalities proves (1). There cannot be an additional
successor in `A`: its good set would be a further disjoint
nonempty subset of this exhausted complement. Nonemptiness follows
from `t_a≥2` in the first-output theorem. This also proves the
bound of `r` on the original number of successors. Applying the
argument to the opposite magma proves the dual assertion.

## The order-forty minimum-four consequences

The degree-five profiles have sizes three or four. If a singleton-`C`
top has `α=4` degree-five successors and `k` of them have
three-element profiles, (1) specializes to the exact identity

\[
                              \boxed{h=16-k.}          \tag{2}
\]

Thus:

- At `h=15`, such a top has exactly one size-three successor.
- At `h=16`, all four successors have size-four profiles.
- At `h≥17`, no such top exists: singleton `C` blocks imply
  `α≤3`, and singleton `P` blocks imply `β≤3`.

These restrictions do not depend on the central count being eight,
nine, or ten. They constrain the degree-five class whenever it is
the first noncentral output degree; they do not prove the full
square/double-square spectrum characterization.
