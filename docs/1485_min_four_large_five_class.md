# Large degree-five classes at minimum degree four

Research note, 19 September 2026. These are analytic necessary
conditions for finite E1485 magmas with minimum degree four, four
central vertices, and least noncentral degree five. They do not
exclude that branch or order forty. The final saturated order-forty
case discussed here is now excluded by the follow-up proofs linked
below. No Lean theorem is asserted.

Write `A` for the degree-five class and `B` for its reciprocal class.
Each `a∈A` has permutation top profiles `U_a,V_a`, one sharp
successor `F(a)∈B`, and one sharp predecessor `G(a)∈B`.
The [minimum-central-count note](1485_minimal_central_count.md#a-first-restriction-at-minimum-degree-four)
gives `|A|≤16`, onto maps `F,G`, and joint injectivity of `(F,G)`.

Assume `|B|≥4`. All permutation profiles have one common parity,
and each of the two profile families uses at most two cosets of the
normal Klein-four subgroup `V₄` in that parity class. Regard a
profile as its actual transversal of the central four-by-four grid;
this avoids a convention choice between a permutation and its inverse.

Within a coset, the four distinct transversals are pairwise disjoint.
Transversals in different cosets of the same parity meet once.

**Theorem.** If both profile families use two cosets, then `|A|≤11`.
If `|A|≥10`, that two-by-two-coset possibility has a particularly
rigid form: the families share exactly one coset; exactly one vertex
uses it on each side, those two vertices are different, and the other
`|A|−2` profiles occupy a three-by-three rectangle in the nonshared
cosets. Thus `|A|≥12` forces at least one profile family into a
single coset.

## 1. Three elementary compatibility rules

Besides joint injectivity, we use:

1. `F(a)=F(c)` for distinct vertices implies `U_a∩U_c=∅`;
   `G(a)=G(c)` implies `V_a∩V_c=∅`. The corresponding sharp
   two-edge paths otherwise have two good middles.
2. If `|V_a∩U_c|≠1`, then `F(a)=G(c)`. Without that sharp
   middle, the endpoint pair `(a,c)` would have to have exactly
   one top middle.
3. If two degree-five vertices have the same `U` profile, their
   `V` profiles lie in the same coset. Otherwise their two `V`
   profiles meet at a single top `v`, and three of the four pairs
   in `U×{v}` are noncentral. Each would have both vertices as
   good middles. There is a dual statement with `U,V` exchanged.

Rule 1 also says that all `U` profiles in an `F`-fiber lie in
one coset and are distinct, so that fiber has at most four members.
Dually the same holds for `V` profiles in a `G`-fiber.

## 2. If the two coset sets agree, there are at most eight vertices

Suppose both sides use the same two cosets. Fix either coset `C`.
Every `V_a` and `U_c` belonging to `C` have intersection size
zero or four, never one. Rule 2 gives

\[
F(a)=G(c)
\]

for every such ordered pair. Thus all vertices whose `U` profile
lies in `C` belong to one `G`-fiber, and there are at most four.
Doing this for the other coset gives `|A|≤8`.

## 3. Different two-coset sets have one common coset

There are only three cosets in the common parity class. If the
two used sets differ, write them as `{P,C}` and `{Q,C}`, with
`P,Q,C` distinct. Put

\[
X=\{a:U_a\in C\},\qquad Y=\{a:V_a\in C\}.
\]

Both sets are nonempty. Rule 2 gives a single `b∈B` such that
`G(x)=b` for every `x∈X` and `F(y)=b` for every `y∈Y`.
In particular, `1≤|X|,|Y|≤4`.

### If the exceptional sets intersect

Suppose `w∈X∩Y`. For every other `x∈X`, the equal `G`-values
make `V_x` disjoint from `V_w`. Since both have the common
parity, `V_x` must belong to the same coset `C`; hence `x∈Y`.
Dually `Y⊆X`, so `X=Y`. Joint injectivity of `(F,G)` now gives
`X=Y={w}`.

All remaining profiles lie in `P×Q`. For each of the four
transversals `U∈P`, let `u(U)` be its unique intersection with
`U_w`; these four points partition `U_w`. Their central successor
labels are distinct. For each `V∈Q`, let `v(V)` be its unique
intersection with `V_w`; their central predecessor labels are
distinct as well.

The good sets of a profile `(U,V)` and `w` can be disjoint only
if `(u(U),v(V))` is central-valued. Equality of the two adjacent
central labels selects exactly four pairs from `P×Q`. Hence there
are at most four additional vertices, and `|A|≤5`.

### If the exceptional sets are disjoint

Write `x=|X|`, `y=|Y|`. Members of `X` have profiles in `C×Q`,
and members of `Y` have profiles in `P×C`. Their common sharp
values make the `x` successor profiles of `X` distinct and the
`y` predecessor profiles of `Y` distinct.

The remaining vertices have profiles in `P×Q`. Rule 3 forbids
their predecessor profile from being one of the `y` profiles
already used by `Y`; the dual rule excludes the `x` successor
profiles used by `X`. Distinct vertices cannot have the same whole
profile pair, because each degree-five profile has twelve good top
pairs. Therefore

\[
\boxed{|A|\le x+y+(4-x)(4-y),\qquad1\le x,y\le4.} \tag{1}
\]

The largest value of (1) is eleven, attained only at `x=y=1`.
Every other choice gives at most nine. In particular, `|A|=10`
or `11` forces two different exceptional vertices and leaves
respectively eight or nine occupied cells of the remaining
three-by-three profile rectangle. This proves the theorem.

## 4. If one side uses a single coset

That coset is disjoint from all cosets used by the other family.
For example, if every `U` belonged to `P` and some `V_a`
also belonged to `P`, Rule 2 would force `G(c)=F(a)` for all
`c∈A`. Surjectivity would give `|B|=1`, contrary to the hypothesis.

Consequently, when `|A|≥12`, one profile family lies in one coset
and the other uses one or both of the two remaining cosets. Rule 3
still applies: a fixed predecessor transversal can be paired only
with successor transversals from one coset, and dually.

## 5. Consequences for the order-forty branch

Suppose in addition that `n=40`. The four possible translation
degrees are `4,5,8,10`; all occur. There are four central vertices
and sixteen tops, so

\[
\alpha=|A|,\quad\beta=|B|,\qquad
\alpha+\beta=20,\quad10\le\alpha\le16,\quad4\le\beta\le10.
\]

Here `β≤α` follows from the onto sharp maps. Every degree-eight
vertex has four top neighbors. Its other neighbors have degree
five, where they are sharp, or degree eight. Reciprocal neighbor
balance therefore gives equal sharp counts in both directions:
the weighted sums are `36+3k⁻` and `36+3k⁺`.

The theorem applies because `β≥4`. For `α≥12`, at least one
profile family uses a single coset. For `α=10,11`, the only other
possibility is the three-by-three rectangle with two exceptional
vertices described above.

At saturation `α=16`, one has `β=4`, and every `F`- and
`G`-fiber has size four. Index `A` by `(G,F)∈B²`. Each
`F`-fiber contains all four predecessor transversals of one coset;
each `G`-fiber contains all four successor transversals of one coset.
These two sets of cosets are disjoint by Rule 2, so one side uses
one coset. On that side each individual transversal occurs four
times, and its four partners fill one entire coset on the other
side. If both sides use one coset, the sixteen profiles form the
complete four-by-four profile rectangle.

These are necessary profile descriptions, not an existence claim
for any surviving diagram and not an exclusion of order forty.

At order forty, the [mixed-profile collapse](1485_order_forty_saturated_profiles.md)
now forces both families into single cosets when `α=16`, and the
[exact finite single-coset check](1485_order_forty_single_coset.md)
excludes that final case. Thus the updated range at this order and
central count was `10≤α≤15`. The further
[analytic near-saturation argument](1485_order_forty_near_saturation.md)
excludes fifteen as well. The subsequent
[arbitrary-product return-matching argument](1485_order_forty_fourteen_exclusion.md)
excludes fourteen without a finite check. The subsequent
[thirteen-vertex profile obstruction](1485_order_forty_thirteen_directions.md)
excludes thirteen after its stated finite incidence reductions, leaving
**`10≤α≤12`**. The bounds in this section describe the reduction before
those additional exclusions.
