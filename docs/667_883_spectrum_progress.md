# E667 and the E883 family: constructive spectrum bounds

Status: 2026-10-05. Neither exact spectrum is known. The complete Lean
construction gives a model at every positive order outside these finite lists.
Orders 3 and 6 are excluded in Lean for both laws; E667 also excludes order 12,
and E883 also excludes order 9.
All other entries remain open.

E667 (3 excluded orders and **15 open orders**):

```
3, 6, 12, 15, 24, 30, 39, 48, 51, 60, 75, 87, 96, 102, 159, 174, 195, 219
```

E883 (3 excluded orders and **20 open orders**):

```
3, 6, 9, 12, 15, 18, 24, 30, 39, 48, 51, 60, 75, 87, 96, 99, 102,
153, 159, 174, 195, 207, 219
```

Both spectra are therefore cofinite with the explicit common cutoff **220**.
The E883 statements transfer through existing spectrum equalities to E1323,
E1526, and all three dual laws. No unsuccessful search is treated as an exclusion.

The current public theorems are `Spectrum.E667.ExtendedBounds.lower`,
`all_large`, and `cofinite`, and the corresponding E883 declarations in
`Spectrum/Equation667883ExtendedBounds.lean`.

The unrestricted order-twelve exclusion is
`Spectrum.not_order_667_12` in `Spectrum/Equation667Twelve/Exclusion.lean`.
It splits the square map into 77 permutation types or three collision
patterns, proves the required relabelling reductions, and checks compact
refutation certificates in Lean. Since E481 has an order-twelve model,
`Spectrum.spectrum_667_ne_481` now separates their spectra; the corresponding
finite FO-definability negative is also formalized. See the
[square-map proof guide](e667_order12_square_map_20261005.md).

## Projective-plane frame: cutoff 220

Order 339 is now proved in Lean. Put Bennett's partial eight-point C3 algebra
on the doubled lines of PG(2,3), giving a partial E63 algebra on thirteen
two-point holes. Inflate by an ordinary thirteen-point E63 model and fill
each hole, together with one common point, with the idempotent 27-point model.
The result has order `13·2·13+1=339`. Only the 26-point frame is checked by
finite computation; the enlargement is a symbolic proof. Its general recipe
also adds idempotent orders 131 and 443. See the
[construction and proof guide](e667_order339_20261005.md).

## Extended designs: cutoff 340

The new construction fills twelve formerly unresolved E667 orders:

```
123, 303, 543, 615, 717, 723, 807, 843, 867, 933, 1203, 1227.
```

For E883 it also fills 387, 927, and 1017. Altogether the underlying idempotent
E63 construction gains 29 orders and has cutoff 689. Its transfers give that
cutoff to E467, E704, E1110, E1279, and E1516 as well.

There are three complementary improvements. First, the transversal-design
gluing theorem now permits any number of groups for which consecutive block
sizes have models. Second, a single extra point can be shared by all group
fillings: a TD(8,q) then gives order `7q+r+1`, using fillings at `q+1` and
`r+1`. Third, compact difference-matrix and projective-plane certificates
supply designs at 40, 50, 76, 100, and 160 that the earlier field-product
construction did not provide. These are reusable designs, not large magma
multiplication tables. The finite checks are explicitly registered as native
Lean checks; the general gluing arguments are ordinary Lean proofs, with no
admitted steps.

| New order | Construction | Essential design or filling |
|---:|---|---|
| 123 | `7*16+10+1` | shared point, fillings 17 and 11 |
| 303 | `7*40+22+1` | difference design at 40, fillings 41 and 23 |
| 387 (E883) | `7*50+37` | quasi-difference design at 50 |
| 543 | `7*76+10+1` | projective-plane design at 76, fillings 77 and 11 |
| 717 | `7*100+16+1` | quasi-difference design at 100, fillings 101 and 17 |
| 723 | `7*100+22+1` | same design, fillings 101 and 23 |
| 807 | `7*112+22+1` | field-product design, fillings 113 and 23 |
| 843 | `7*112+58+1` | same design, fillings 113 and 59 |
| 867 | `7*112+82+1` | same design, fillings 113 and 83 |
| 933 | `7*128+36+1` | field design, fillings 129 and 37 |
| 1017 (E883) | `31*32+25` | wider field design, block sizes 31 and 32 |
| 1203 | `32*37+19` | wider field design, block sizes 32 and 33 |
| 1227 | `7*160+107` | binary difference design at 160 |

Products supply 615 from 123. The remaining inherited improvements are
replayed by `scripts/spectrum_667_extended_bounds.py`, which generates the
Lean construction DAG and checks the coverage of the previous exception lists.
See the individual design modules under `Spectrum/Equation63/` and their
companion JSON files for provenance and the exact finite certificates.

## Orders 12 and 15: structural research leading to the exclusion

Order 12 is now excluded by the exhaustive proof above; order 15 remains
unresolved. The earlier structural results below remain independently proved.
Constant-diagonal models are
excluded at both orders by a general Lean theorem: twisting such a model by
its common-square translation gives a semisymmetric loop, so its order cannot
be divisible by three. The more general square-fiber and translation-cycle
identities are also proved in `Spectrum/Equation667ConstantDiagonal.lean`.

The quotient analysis shows that a hypothetical model at either order must
be simple. Uniform fiber sizes and idempotent-fiber inheritance are proved
in `Spectrum/Equation667Quotients.lean`. The order-15 obstruction over the
idempotent-free five-element quotient is proved in
`Spectrum/Equation667FiberThree.lean`, even for arbitrary three-element fiber
operations: every Latin three-point block is affine, and a product of its
coefficient identities gives a sign contradiction. The size-2 and size-4 idempotent results are also proved in Lean using only
small unary-permutation checks, and `Spectrum.E667.quotient_card_twelve` in
`Equation667SimpleTwelve.lean` completes the order-12 simplicity theorem.
The five-element classification and the order-15 simplicity theorem are now
also fully formalized; see the [order-fifteen note](e667_mace4_and_order15.md).

The [2026-10-04 structural research](e667_structure_20261004.md) adds a
certificate-free Lean obstruction to commutative models at every order
three modulo four, covering all remaining open odd orders. It also proves
that a quotient containing a square-map cycle of length one or two cannot
have three-element fibers. Complete pen-and-paper arguments identify the
commutative idempotent subclass with five-point design algebras and split
affine models into three polynomial components away from primes 2 and 5.
These restrictions leave the unrestricted spectrum lists unchanged.

Additional bounded SAT searches and nonlinear isotope searches have not found
models. The precise restrictions and case outcomes are saved separately;
a timeout neither excludes an order nor establishes its improbability. In
particular, the standard normalized search chooses a non-idempotent element
as zero whenever possible. Its first-row-fixed-at-zero branch therefore
covers fully idempotent models; it does **not** exclude mixed-idempotent models.
The new one-idempotent search mode omits that normalization. The strengthened
searches reduce order 12 to 51 remaining canonical row forms; see the
[search report](e667_incremental_searches.md) for the exact scopes, saved near-model,
and bounded repair results.

## Nonlinear constructions and regular-action obstructions

The [nonlinear construction note](e667_nonlinear_constructions_20261004.md)
explains noncommutative, non-idempotent examples through involutive output
twists, binary choices on five-point design blocks, and directed triangles
built from nonabelian multiplication. The twist theorem and the explicit
arbitrary-function family on F₅×F₂ are proved in Lean. The old ten-point
square-retraction counterexample is recovered from a five-bit function;
its extension class has exactly three isomorphism types. Explicit design
examples at 20 and 42 are independently checked research constructions.

External CP-SAT exhaustions exclude regular automorphism-group constructions
over all five groups of order 12 and the cyclic group of order 15. These are
restrictions on symmetric constructions, not exclusions of either spectrum
order. No unrestricted spectrum entry changes in this pass.

## Earlier construction stages

The following sections record the prior cutoffs and how they were obtained.
The current lists and cutoff are the ones above.

## New homogeneous seeds at 31 and 41

The Lean-checked idempotent E63 seeds at 31 and 41 remove six more E667
exceptions (255, 321, 327, 489, 510, 654) and seven E883 exceptions
(255, 321, 327, 423, 489, 510, 654). In particular, the new order 31 seed completes
the `7·32+31=255` field-design construction. All bounds below have been
regenerated using these seeds; their explicit tail remains 1228. See
[the new homogeneous constructions](63_homogeneous31.md) for the compact
profiles, proof declarations, and the 33 new idempotent orders they supply.

## Complete constructive argument

Write E63 as `p(y,p(x,p(x,y)))=x`. Suppose also that `p(x,x)=x`.
Then E667 holds for `p` immediately. Define

```
q(x,y) = p(x,p(x,y)).
```

This operation is idempotent, and two applications of E63 give

```
q(y,q(q(x,y),y))
  = p(y,p(y,q(q(x,y),y)))
  = p(y,q(x,y))
  = x.
```

Consequently `q` satisfies E883. These two transfers require no finiteness.
The explicit idempotent E63 construction in
[63_idempotent_tail.md](63_idempotent_tail.md) supplies every order at least
1480, and all smaller orders outside its finite certificate of possible
exceptions. It uses affine seeds, products, singular products, transversal
designs, and strong induction; it does not invoke Wilson's existence theorem.
The newly reconstructed idempotent seed of order 32 is checked directly by the
Lean kernel. A companion-matrix construction supplies every cube order.
The finite-field supplement below improves the cutoff to 1228.

Semisymmetric loops supply every positive order congruent to 1 or 2 modulo 3,
with the order-7 model supplied separately. Finally take products. Closing these
families under multiplication, together with the finite-field supplement, gives
the two displayed lower bounds. The original coverage calculation is replayed
in `Spectrum/Equation667883Bounds.lean`. The intermediate field bounds are in
`Spectrum/Equation667883FieldBounds.lean`, generated by
`scripts/spectrum_667_883_field_bounds.py`.

Two additional algebraic constructions are formalized in
`Spectrum/Equation667883.lean`:

- **All squares for E667.** On `R²`, let `J(u,v)=(-v,u)` and define
  `p(x,y)=J(x+y)`. Expanding E667 and using `J²=-I` proves the identity.
  Take `R=Z/n` to obtain order `n²`.
- **All fourth powers for E883.** On `R⁴`, let `A` be the companion matrix of
  `t⁴+t³+t²+1`, and set `B=-(A²+A+I)`. Then `BA²=I` and
  `A+2AB²+B³=0`. The operation `p(x,y)=Ax+By` satisfies E883 because its right
  side expands to `BA²x+(A+2AB²+B³)y=x`. Take `R=Z/n`.

The order-6 exclusions in `Spectrum/Equation667883Small.lean` exhaust every
six-element magma table. Lean checks the SAT refutations via LRAT. These
proofs assume neither Latin cancellation nor a symmetry restriction.

## Finite-field designs improve the cutoff to 1228

Over any finite field F with at least seven elements, choose seven distinct
slopes. The coordinates `b` and `a+cᵢb` of lines indexed by `(a,b)` give a
TD(8,|F|): every pair of coordinates determines `(a,b)` uniquely because a
nonzero slope difference is invertible. Taking products of two designs gives
a design whose group size is the product of their group sizes.

The earlier certificate used cyclic designs and the special designs at
25, 27, and 36. The field and product constructions add useful choices such
as 8, 32, 56, 88, 136, 144, and 189. With existing idempotent group fillings,
the same seven-group gluing theorem supplies these previously open orders:

| Order | Decomposition `7q+r` | Newly supplied for |
|---|---|---|
| 63 | `7·8+7` | E883 family |
| 447 | `7·56+55` | both |
| 633 | `7·88+17` | both |
| 699 | `7·88+83` | both |
| 975 | `7·136+23` | both |
| 1059 | `7·136+107` | both |
| 1119 | `7·144+111` | both |
| 1143 | `7·144+135` | E883 family |
| 1479 | `7·189+156` | both |

The group sizes and truncated sizes in this table already have idempotent E63
models. The designs at 56, 88, 136, 144, and 189 are products of field designs
at `(7,8)`, `(8,11)`, `(8,17)`, `(9,16)`, and `(7,27)` respectively. Existence
of a field design does not require an idempotent model of that field's order;
only the final group size needs a filling.

Closing the new constructions under products and singular products supplies
25 additional idempotent orders in total. Their Lean proofs are generated in
`Spectrum/Equation63/FieldBounds.lean`, using the general field and product
theorems in `FieldDesign.lean`. Above 1227 the old idempotent certificate had
only the gap 1479, which is now filled. Hence every order at least **1228**
has an idempotent E63 model and consequently models of both target laws.
No table witnesses or external search certificates are needed for this
improvement. The subsequently proved order 31 seed now supplies the missing group filling
in `7·32+31=255`; the new homogeneous-seed section above records the resulting
improvements.

## Search results and remaining obstacles

Finite models of either law are quasigroups, as proved independently in
`Spectrum/Equation667883Small/Basic.lean`. This permits Latin constraints in
exploratory searches without losing finite models.

E667 searches at 12 and 15 remain inconclusive. At 12, both unrestricted and
constant-diagonal SAT searches reached one million conflicts; finite-domain
searches at 12 and 15 also timed out. Restricted translation-equivariant
constructions over `C₂² × C₃` at order 12 and selected shifts over `C₁₅`
were exhaustively ruled out within those restricted families only.
A first-row cycle decomposition at order 12 covered all 195 canonical forms.
The initial pass refuted 59 forms; a further 20,000-conflict pass on each
remaining form refuted seven more. The other 129 forms remain unresolved,
and no model was found. These partial refutations do not exclude order 12.
Four further 100,000-conflict searches imposed only the automorphism
`x ↦ x+s`: shifts 4 and 6 at order 12, and shifts 3 and 5 at order 15.
All four were inconclusive. These constraints allow more operations than
the fully translation-equivariant construction above, but still restrict
the model class.
A deeper two-million-conflict pass refuted the order-12 shift-4 case in
128 seconds: no E667 model of order 12 can have that fixed-point-free
order-3 automorphism. The order-15 shift-3 retry hit its 150-second wall
limit. The order-12 refutation is external and restricted to that symmetry
class; it is not a nonexistence certificate for all order-12 magmas.

Initial E883 order-9 searches were inconclusive, including a two-million-conflict
Latin SAT run and a 90-second finite-domain run. A stronger symmetry reduction
then gave a complete external refutation, described below. The previously found
idempotent order-21 model is now subsumed by the general idempotent construction
and transfer.

A tempting structural shortcut is false for both laws: squaring need not
preserve multiplication. Independently checked counterexamples of orders nine
for E667 and eight for E883 are saved in `data/spectrum/667_883_research.json`,
alongside the exploratory search outcomes. These are explicit tables checked
in Python, not new Lean declarations. They prevent reliance on that structural
assumption; the new spectrum bounds do not depend on them.

## Lean-checked order-nine refutation for E883

Every finite E883 model is Latin. In a nontrivial Latin square some row is not
the identity permutation: if every row were the identity, each column would
be constant. Choose a nonidentity row and relabel its index as 0. Conjugating
its row permutation by a permutation fixing 0 puts it in a canonical form:
first the cycle containing 0, then the other cycles in decreasing order of
length, with consecutive labels within each cycle.

There are 67 such forms at order nine, described by the length of the cycle
containing 0 and an integer partition of the remaining number of elements.
Exactly one is the identity permutation. Exhaustive SAT refutations rule out
all **66 nonidentity forms**. The remaining identity-row search is inconclusive,
but is unnecessary because the distinguished row was chosen to be nonidentity.
This is a complete external finite nonexistence argument, not an inference
from a search timeout.

The original per-case outcomes and argument are in
`data/spectrum/883_order9_refutation.json`. Reproduce the external search passes
with `python3 scripts/spectrum_883_nine_search.py`.

The complete Lean replay is now in `Spectrum/Equation883Nine/`. It checks the
canonicalization of all 362,880 permutations, proves the relabeling and Latin
table bridges, and checks LRAT refutations for all 66 nonidentity rows. Every
row refutation succeeded at its original 60-second SAT cap. These finite
computations use the registered native-checking machinery; the proof contains
no admitted steps and does not trust the external search reports. The public
theorem is `Spectrum.not_order_883_9` in `Spectrum/Equation883Nine.lean`.

In particular, the two spectra differ at order nine: E667 has a model there,
whereas E883 and its five companion laws do not.

The smallest remaining mathematical targets for both families are now orders
**12 and 15**. A model at either order would also supply many multiples.

## Why further affine searches cannot close the remaining orders

There is a complete obstruction for affine operations on finite abelian groups.
This argument is mathematical only; it is not a new Lean declaration and is not
used to exclude arbitrary magmas in the catalogue.

Suppose `x*y = Ax + By + c`, where A and B are endomorphisms of a finite abelian
group. Either law forces the operation to be Latin, hence A and B are
automorphisms. Comparing coefficients in E667 gives

```
A = -B³,
B⁸ - B⁶ - B⁴ - I = 0.
```

The polynomial factors over the integers as

```
t⁸ - t⁶ - t⁴ - 1 = (t²+1)(t³-t-1)(t³-t+1).
```

All three factors are irreducible over F₃, with degrees 2, 3, and 3.
Consequently the exponent of 3 in the group order belongs to
`{2a+3b : a,b ≥ 0}`. In particular it cannot be 1. **Every one of the 35
remaining E667 orders has exponent exactly 1**, so none can have an affine
model on an abelian group.

For E883, comparison instead gives `BA²=I` and `A+2AB²+B³=0`. Thus
`B=A⁻²` and

```
A⁷ + 2A³ + I = 0,
t⁷ + 2t³ + 1 = (t³-t²+1)(t⁴+t³+t²+1).
```

The factors are irreducible over F₃ of degrees 3 and 4. For the quartic,
there are no roots, and its remainders modulo the three monic irreducible
quadratics `t²+1`, `t²+t+2`, and `t²+2t+2` are respectively `1-t`, `t`,
and `-1`. Hence the exponent of 3 must belong to `{3a+4b : a,b ≥ 0}`;
exponents 1, 2, and 5 are impossible for affine models. All the remaining
E883 orders have one of these prohibited exponents.

For completeness, the dimension argument applies to arbitrary finite abelian
groups, not just elementary abelian ones. On the 3-primary subgroup H, each
quotient `3ⁱH / 3ⁱ⁺¹H` is an F₃-vector space. The induced automorphism obeys
the same polynomial, so its characteristic polynomial has only the listed
irreducible factors. Its dimension is therefore a sum of their degrees.
Summing these dimensions gives the exponent of 3 in `|H|`. Constants c
do not affect the coefficient identities. This leaves nonlinear quasigroup
constructions as the relevant route for all the remaining orders.

## Order-twelve subclass restrictions

The latest pass has completely formalized the exclusion of commutative,
idempotent, associative, left-unital, and right-unital E667 models at order
twelve. Finite E667 models are necessarily quasigroups, so that property is
not a further subclass exclusion. The unrestricted existence problem and the
17-order open list are unchanged. Proof sketches, certificate sizes, and
reproduction commands are in `e667_order12_subclasses.md`.

## Order-fifteen restrictions

Simplicity at fifteen is now fully formalized, including the previously
external idempotent-free five-point quotient classification. Commutative and
globally idempotent order-fifteen E667 models are also excluded in Lean.
Right identity alone remains unresolved at fifteen; general existence remains
open. See `e667_mace4_and_order15.md` for the proofs and Mace4 search outcomes.

## Further restrictions at twenty-four and beyond

The next pass classified the idempotent-free eight-element model and proved
that it has no three-element-fiber extension. Consequently an order-24 model
can have quotient orders only 1, 2, 12, or 24; a nonsimple model at 24 would
give a model at 12. A separate descent through square-map images excludes
commutative E667 models at **every order `3 * 2^k`**, including 24, 48, and 96.
All these results are formalized in Lean. The 17 unresolved orders and the
340 cutoff are unchanged. See [the follow-up report](e667_followup_20261002.md)
for the proofs, the 156 KB classification certificate, and further design
searches.

## Idempotent seed searches

A subsequent campaign tested idempotent models at orders with and without
known ordinary E667 models. It excluded idempotent order **13 in Lean**, and
idempotent order **16 by an external exhaustive case argument**. At order 20,
20 of the 39 possible first-row cycle patterns were initially exhausted.
The October 4 follow-up exhausts two more, ruling out 3-cycles globally in
the E229 parastrophe and leaving 17 row types unresolved, externally.
Searches at 22, 24, and 38 found no new positive seed. Thus the 17 unresolved
ordinary orders and the cutoff 340 are unchanged. The
[idempotent-search report](e667_idempotent_searches_20261003.md) records the
156 attempts, construction priorities, and a counting obstruction to making
an idempotent order-38 seed by direct PBD gluing from the existing smaller seeds.

## Nonlinear constructions and structural classification

The [2026-10-04 formalization report](e667_formalization_20261004.md) records
the completed Lean proofs of the binary-extension classification, its three
ten-point isomorphism types, and the design construction with independent
nonlinear choices on each five-point block. It also proves the intrinsic
five-point design of every finite commutative idempotent E667 algebra,
constructs explicit nonabelian-group examples, and formalizes the affine
coefficient criterion and three-kernel decomposition away from two and five.

A uniform affine obstruction now excludes affine models at **all 17 remaining
open orders**: divisibility by three forces divisibility by nine. The
unrestricted spectrum and cutoff 340 are unchanged; the remaining existence
problems require nonlinear constructions or general nonexistence arguments.
The same report now gives a complete paper characterization of the affine
spectrum: a positive n is possible exactly when every prime dividing n only
once admits a root of `t^8-t^6-t^4-1` modulo that prime. Necessity and the
scalar, square, cube, and product constructions are in Lean; the final
prime-factorization assembly has not yet been packaged as one Lean theorem.

The [open-order follow-up](e667_open_orders_20261004.md) extends the obstruction
to **all finite medial models**, proves a proper-submagma size bound, and
formally excludes every regular-group construction at orders 2 modulo 4.
External SAT also excludes all regular automorphism groups at 20 and 24,
including non-idempotent models. Further seed, isotope, plane, and cyclic
design searches have supplied no new positive spectrum order.
