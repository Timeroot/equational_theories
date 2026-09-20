# Four central and nine top vertices: degree four forces two singleton classes

Research note, 18 September 2026. Suppose the minimum translation
degree is three, there are four central and nine top vertices, and
four is the least noncentral degree. Then the degree-four class `A`
and its reciprocal class `B` satisfy

\[
\boxed{A=\{a\},\quad B=\{b\},\quad
a\Rightarrow b\Rightarrow a,\quad a*a=b,\quad b*b=a.}
\]

Moreover the three top predecessors and three top successors of `a`
are disjoint. The sharp-degree and parameter-separation arguments are
analytic; the final singleton bound uses an explicit 285-diagram
incidence check, not a SAT result or Lean proof. No assertion assumes
order 24 or a bound on the number of degrees. The singleton footprint
is now excluded at every order by the
[degree-five profile and refined-packing argument](1485_four_central_degree_four_exclusion.md).
This note records the singleton reduction used in that proof.

## The order-24 profile argument is independent of the order

Write `H` for the unique top of central profile `(2,2)`, `U₁,U₂`
for the two of profile `(1,2)`, and `V₁,V₂` for those of profile
`(2,1)`. Put `R=P_H`, `C=C_H`. The singleton predecessor labels
of `U₁,U₂` are the two members of `Z\R`; the singleton successor
labels of `V₁,V₂` are the two members of `Z\C`.

A least-degree-four vertex has sharp degree one or two. In the
second case its two top predecessors partition `Z` by their double
predecessor sets, and its two top successors do the same by double
successor sets. Thus these profiles lie in `{H,V₁,V₂}` and
`{H,U₁,U₂}`, respectively.

If either profile contains `H`, the central rectangles overlap.
For example, if both do, the remaining vertical has predecessor
pair `Z\R` and the remaining horizontal has successor pair `Z\C`;
their rectangles overlap at their singleton predecessor/successor
labels. If only the predecessor profile contains `H`, its vertical
contains both singleton predecessor labels of the horizontals, and
the successor pairs of the two horizontals partition `Z`. One of
those horizontals therefore overlaps that vertical. The last case
is dual.

Otherwise the profiles are `{V₁,V₂}` and `{U₁,U₂}`. A top
fiber at the degree-four output has its two sharp inputs and one
top input. Its central-middle submatrix is consequently a `2×2`
permutation matrix. Its entries say precisely that the singleton
successor label of `V_j` equals the singleton predecessor label
of `U_i`. Thus `Z\C=Z\R`, or `C=R`. But then `H⇒Z⇒H`
has two central middles, a contradiction.

This is the argument in the final section of the
[small-central order-24 note](1485_order_twenty_four_small_central.md#the-remaining-four-central-case-has-no-sharp-degree-two-vertex-in-a).
Every step above remains valid at arbitrary order.

## The finite profile bound and its consequence

Every member of `A` therefore has sharp degree one and three top
neighbors in each direction. Its central-middle submatrix is a
`3×3` permutation matrix. Different members have different profiles:
any of the six noncentral endpoint pairs in one profile has a unique
good middle of degree four.

The [explicit finite incidence lemma](1485_order_twenty_four_four_central_finite.md#a-finite-central-rectangle-lemma)
bounds the number of such profiles by four. Its enumeration uses
only the central/top profile, not the order. Therefore `|A|≤4`.
Every vertex of reciprocal degree needs a sharp predecessor in `A`,
and each member of `A` has only one sharp successor. Hence `|B|≤|A|`.

## A degree-four vertex separates all central parameters

Fix `a∈A`, and suppose two central parameters `h,k` gave the same
global auxiliary relation `B_h=B_k`. For a central parameter `h`,
the set `B_h(a)` consists of the unique sharp successor of `a`
and two of its three top successors. The omitted top is the unique
`v∈TopSucc(a)` for which `(h*a)*v` is central: the central-middle
matrix on the two top profiles is a permutation matrix.

Different rows of that permutation matrix omit different tops.
Equality `B_h(a)=B_k(a)` therefore implies `h*a=k*a=t`.
The two central parameters then belong to the central predecessor
set `P_t`.

Dually, equality of the predecessor sets `B_h^-(a)=B_k^-(a)`
implies `a*h=a*k=u`, and puts both parameters in the central
successor set `C_u`. But `|P_t∩C_u|≤1`, by uniqueness of a
central middle. Thus `h=k`.

Consequently all global auxiliary relations for distinct central
parameters are distinct. In particular, no two central rows can be
equal, and no two central columns can be equal: either equality
would make the associated auxiliary relations coincide.

## The remaining finite profiles force singleton classes

The executable check is

```text
python3 scripts/1485_m4h9_degree_four_check.py
```

It imports the existing exhaustive 285-diagram generator. Among
diagrams admitting degree-four profiles, the counts are:

| Equal central rows or columns? | Number of profiles | Number of diagrams |
| --- | ---: | ---: |
| No | 1 | 24 |
| Yes | 2 | 24 |
| Yes | 4 | 6 |

The other 231 diagrams admit no such profile. The analytic
parameter-separation argument excludes both sharing rows of the
table. Each remaining diagram has only one profile, and its top
predecessor and successor sets are disjoint. These remaining
diagrams form six orbits under central relabeling and duality.

Every profile has six noncentral top pairs, all with good middle
`a`; hence two distinct degree-four vertices cannot realize the
same profile. Since degree four occurs, `A={a}`. The reciprocal
class is nonempty and has size at most `|A|`, so `B={b}`. Existence
of sharp neighbors gives both `a⇒b` and `b⇒a`. Unique goodness
of these sharp two-edge paths gives `a*a=b` and `b*b=a`.

For comparison, the same script also checks the weaker bound obtained
by merely requiring good sets of different profiles to be disjoint:
231 diagrams have maximum packing size zero, 52 size one, and two
size two. Parameter separation eliminates the two-vertex possibility.

## The four-degree consequence

With exactly four degrees, the classes are `Z,A,B,T`, and so

\[
n=4+9+|A|+|B|=15.
\]

But `12|n`, and the reciprocal middle degree is strictly greater
than four, so `n≥24`. This excludes the entire four-degree branch,
including the previously unresolved square order 36 in this profile.
