# E667 structural formalization, 2026-10-04

Update, October 5: order 339 is now proved and the E667/E883 tails are 220.
See [the projective-frame construction](e667_order339_20261005.md).
The dated account below records the earlier state.

This pass formalizes the nonlinear constructions and structural arguments in
[e667_nonlinear_constructions_20261004.md](e667_nonlinear_constructions_20261004.md)
and [e667_structure_20261004.md](e667_structure_20261004.md).
The formalized results below use ordinary Lean proofs: no new `sorry`,
`native_decide`, external solver axiom, or SAT proof file is needed. The final
assembly of the complete affine spectrum is separately marked as a paper proof.

The unrestricted spectrum is unchanged. These 17 orders remain open:

```
12, 15, 24, 30, 39, 48, 51, 60, 75, 87, 96, 102, 159, 174, 195, 219, 339.
```

## Binary extensions: construction and classification

Every finite E667 extension with two-element fibers has, after labelling the
fibers, the form `(i,a)*(j,b)=(q(i,j),a+b+C(i,j))`. The E667 law is equivalent
to a linear cocycle identity for C together with E667 for q. Moving the origin
in fiber i by `h(i)` changes C by `h(i)+h(j)+h(q(i,j))`. These statements are
proved for arbitrary quotients in
[Equation667BinaryExtensions.lean](../equational_theories/Spectrum/Equation667BinaryExtensions.lean):
`law_iff`, `every_fiber_extension`, `shift_hom`, and `gauge_law`.
[BinaryQuotients](../equational_theories/Spectrum/Equation667BinaryQuotients.lean)
provides the coordinate-free version, `quotient_coordinates`: an arbitrary
surjective homomorphism with two-element fibers admits exactly this description,
with the prescribed quotient map as first-coordinate projection.

For the five-point mean algebra, put each fiber's unique idempotent at zero.
Every remaining cocycle is exactly

```
C(i,j)=v(i)+v(2j-i),      v : F5 -> F2.
```

There are exactly **three isomorphism classes**, represented by v with zero,
one, or two nonzero entries. They have respectively **100, 36, and 68
commuting ordered pairs**, which separates them under arbitrary isomorphisms.
This is a classification of all ten-element E667 algebras with a surjective
homomorphism onto this five-point quotient, not of all ten-element E667 algebras.

| File | Main declarations |
|---|---|
| [BinaryFiveProperties](../equational_theories/Spectrum/Equation667BinaryFiveProperties.lean) | `square_hom_iff`, `commutative_iff_constant`, `medial_iff_constant`, `idempotents_closed_iff`, `idempotents_card` |
| [BinaryFiveCompleteness](../equational_theories/Spectrum/Equation667BinaryFiveCompleteness.lean) | `normalized_complete` |
| [BinaryFiveIsomorphism](../equational_theories/Spectrum/Equation667BinaryFiveIsomorphism.lean) | `exists_representative`, `representative_commuting_card`, `representatives_distinct` |
| [BinaryFiveAutomorphisms](../equational_theories/Spectrum/Equation667BinaryFiveAutomorphisms.lean) | `automorphism_shape`, `automorphismEquiv`, `automorphism_card`: group orders 20, 4, 2 |
| [BinaryFiveClassification](../equational_theories/Spectrum/Equation667BinaryFiveClassification.lean) | `classify_extension`, `classify_quotient` |

The completeness proof consists of short linear combinations of scalar
cocycle identities. Its generator is
[spectrum_667_binary_classification.py](../scripts/spectrum_667_binary_classification.py).
The small classification and commuting-pair counts use ordinary kernel
computation, on 32 binary functions or 100 ordered pairs respectively.

## Five-point designs and independent nonlinear choices

In a finite commutative idempotent E667 algebra, every distinct pair generates
exactly five points, with the mean-algebra multiplication table. The intrinsic
five-element subalgebras therefore form a 2-(n,5,1) design. Lean proves the
unique cover, coordinates on every block, and the two counting identities

```
4 * (number of blocks through a point) = n - 1,
20 * (number of blocks) = n * (n - 1).
```

Thus every nonempty such algebra has **n = 1 or 5 modulo 20**. The same
restriction applies to the nonempty idempotent subalgebra of any globally
commutative E667 model. This does not apply to unrestricted E667 models.

The proofs are in
[CommutativeBlocks](../equational_theories/Spectrum/Equation667CommutativeBlocks.lean)
(`five_embedding`) and
[CommutativeDesign](../equational_theories/Spectrum/Equation667CommutativeDesign.lean)
(`cover`, `block_coordinates`, `point_count`, `pair_count`, `card_mod_twenty`,
`idempotents_mod_twenty`). No general design-existence theorem is assumed.

On an arbitrary five-point design, choose an independent binary function on
each block and use the ten-point construction locally. This gives a global
E667 operation on twice the point set. Its square is `(i,a)*(i,a)=(i,0)`.
Any nonconstant block makes the global operation noncommutative and nonmedial.
The base projection remains a homomorphism even though squaring need not be.

[BinaryDesign](../equational_theories/Spectrum/Equation667BinaryDesign.lean)
proves these facts without requiring a finite design.
`square_hom_iff` characterizes when squaring is a homomorphism: every block
function must be constant. `medial_iff` gives the exact mediality criterion:
the same condition, together with mediality of the base operation.
[BinaryDesignClassification](../equational_theories/Spectrum/Equation667BinaryDesignClassification.lean)
proves that these choices exhaust all normalized binary extensions and gives
a bijection with the independent block data. There are exactly **2^(4b)**
normalized labelled operations for b blocks, and exactly one is commutative.
The zero-data operation may still be nonmedial when the base design is.
[BinaryDesignCount](../equational_theories/Spectrum/Equation667BinaryDesignCount.lean)
proves the exact count **2^(n+4b)** before normalization: each of the n fibers
has an additional independent choice of origin. `allExtensionEquiv` proves
that this includes every possible E667 multiplication table on the two-point
fibers, not just tables initially supplied in the additive form.
Exactly **2^n** of these labelled cocycles are commutative (`commutative_count`).
Their diagonal entries determine the whole cocycle (`symmetric_iff`), and
`commutative_isomorphism` identifies every one with the direct product of the
base and the two-element group, preserving the quotient projection.

[BinaryDesignExistence](../equational_theories/Spectrum/Equation667BinaryDesignExistence.lean)
extracts the blocks and coordinates from any nontrivial finite commutative
idempotent E667 algebra, preserving its actual multiplication as the quotient.
`exists_deformation` proves the existence of a noncommutative, nonmedial double
cover with exactly n idempotents.

## Nonabelian groups

[GroupConstructions](../equational_theories/Spectrum/Equation667GroupConstructions.lean)
proves two complementary facts. An operation `α(x)β(y)c` made from group
automorphisms can satisfy E667 only if the group is abelian. In contrast,
regular group actions give the more general form `x*h(x^-1*y)`, with an exact
one-variable E667 criterion. The regular-profile and commutativity criteria
are formalized; the saved CP-SAT exclusions are still external results.
`regular_latin_iff` also proves that the operation is a quasigroup precisely
when both `h(t)` and `t^-1*h(t)` are bijections, without requiring finiteness.

[GroupMendelsohn](../equational_theories/Spectrum/Equation667GroupMendelsohn.lean)
constructs a Mendelsohn system on three copies of any group plus a common
point, using a filling on the group plus one point. Cross-copy products use
nonabelian multiplication directly. Adjoining an identity gives an E667
loop of order **3|G|+2**, with exactly one idempotent. Noncommuting group
elements force both noncommutativity and nonmediality of the loop. For S3,
the filling is the affine seven-point system, producing a formalized
**20-element example**. Its chosen coordinates need not match the JSON labels.
[LatinTriangles](../equational_theories/Spectrum/Equation667LatinTriangles.lean)
further generalizes the construction to two independent Latin squares.
Neither square needs to be associative or idempotent, and both can be
recovered from the labelled result (`recover_left`, `recover_right`).

[Frobenius21](../equational_theories/Spectrum/Equation667Frobenius21.lean)
formalizes the explicit profile over `C7 ⋊ C3`. Group associativity is proved
symbolically, using nine checks for the C3 action, and E667 uses only **21
profile equations**. The resulting 21-point algebra is commutative,
idempotent, and nonmedial. `nonlinear_double_cover` then proves the existence
of a **42-point noncommutative, nonmedial algebra with exactly 21 idempotents**,
retaining the explicit 21-point algebra as quotient. Neither 20 nor 42 is a
new positive spectrum order. For this quotient, `binary_extension_counts`
proves that there are exactly **2^105** labelled binary cocycles, or **2^84**
after normalizing the fibers.

## Affine structure away from two and five

[AffineStructure](../equational_theories/Spectrum/Equation667AffineStructure.lean)
proves the exact affine criterion on an arbitrary abelian group. For
`x*y=A(x)+B(y)+c`, E667 is equivalent to

```
A = -B^3,
P(B)=0,   P(t)=(t^2+1)(t^3-t-1)(t^3-t+1),
K(B)c=0,  K(t)=-(t^2+1)(t^3-t-1).
```

No prior commutativity or invertibility assumption on A and B is required.
Every such affine operation is medial. `no_affine_representation` therefore
proves that a nonmedial E667 example cannot be disguised as an affine operation
on any abelian group by changing labels.

A Bézout identity for `H=t^3-t+1` and K has right-hand side 10. It follows
that **every affine E667 model whose order is coprime to ten has an
idempotent**. Translation by that idempotent removes c.

[AffineDecomposition](../equational_theories/Spectrum/Equation667AffineDecomposition.lean)
proves the complete three-kernel splitting, using explicit projection
numerators and division by ten. The summands have respectively

* `B^2=-1` and `A=B` (Gaussian);
* `A=-1-B` (negative of an idempotent affine E63 operation);
* `A=1-B` (idempotent affine E63).

`unique_splitting` proves existence and uniqueness for every element;
`kernel_invariant` proves that B preserves the summands. The three coefficient
identifications and removal of c are also formalized. This replaces the
previous pen-and-paper module-CRT argument with explicit Lean identities.

## A uniform affine exclusion at every remaining open order

[AffineThree](../equational_theories/Spectrum/Equation667AffineThree.lean)
proves **3 divides n implies 9 divides n** for affine E667 algebras on finite
abelian groups. In particular `not_affine_of_mod_nine` excludes every order
3 or 6 modulo nine. All 17 remaining open orders have one of those residues.
This concerns affine models only, not unrestricted existence.

The proof is structural. Cauchy's theorem supplies a nonzero element a of
order three. The polynomial P(B)=0 prevents B(a) from being 0, a, or -a:
either of the last two possibilities makes P(B)a=-2a, which cannot vanish
for a nonzero element of order three. Thus a and B(a) generate an embedded
copy of C3 × C3. Its order nine divides the carrier order by Lagrange's
theorem. No enumeration of endomorphisms or group structures is used.

The general version is proved in
[AffinePrime](../equational_theories/Spectrum/Equation667AffinePrime.lean):
for any prime p at which P has no root, divisibility by p forces divisibility
by p². This applies to **31 and 47** as well as three. The proof uses Cauchy's
theorem and an injective homomorphism from Fp², with no classification of
finite abelian groups.

[AffineCyclic](../equational_theories/Spectrum/Equation667AffineCyclic.lean)
proves the exact cyclic criterion: an affine E667 operation on Z/n exists
if and only if P has a root modulo n. Root obstructions pass to multiples;
in particular no cyclic additive group of order divisible by three supports
an affine E667 operation. The known E667 models at prime orders 31 and 47
are therefore necessarily nonaffine over any abelian group. This last
conclusion is about every possible abelian-group coordinate system.

## Complete affine spectrum: assembling the constructions

There is now a complete pen-and-paper characterization of the **affine**
spectrum. For a positive integer n, an affine E667 model of order n exists
if and only if every prime p with `p | n` and `p^2 ∤ n` admits a root of P
modulo p. The necessity is formalized in `affine_prime_square_dvd`.

For sufficiency, factor n into prime powers. If P has a root r modulo p,
the operation `x*y=-r^3*x+r*y` on Fp is an E667 seed of order p; its e-fold
product gives order p^e. For a prime without such a root, the hypothesis
says its exponent e is at least two. Every integer e at least two is
`2a+3b` for nonnegative a,b (use b=0 for even e, b=1 for odd e).
The integral matrices

```
J(x,y)=(-y,x),                J^2+1=0,
T(x,y,z)=(z,x+z,y),           T^3-T-1=0
```

annihilate P, so `u*v=-B^3(u)+B(v)` gives affine E667 models on Fp² and
Fp³. Taking a copies of the former and b copies of the latter gives order
p^e. Finally take the product over the primes. The n=1 case is the empty
product. This proves sufficiency, including primes two and five: the
construction does not divide by ten. All the groups used can have elementary
abelian Sylow subgroups, and all constants can be zero.

[AffineUniversal](../equational_theories/Spectrum/Equation667AffineUniversal.lean)
formalizes both integral matrices, their annihilating identities, their E667
laws over **any abelian group**, the square/cube cardinalities over Z/n, and
preservation of the affine form under direct products (`product_law`).
The scalar criterion is in `AffineCyclic`. The final assembly over prime
factorizations is proved above on paper; it is not yet packaged as a single
Lean spectrum-characterization theorem. The unrestricted spectrum is not
being characterized by this result.

In `AffineUniversal`, `coefficient_bijective` also extracts the explicit inverse
`B^-1=B^7-B^5-B^3` from P(B)=0. Consequently both affine coefficient maps
are automatically bijective (`affine_coefficients_bijective`), and every
affine E667 algebra is a quasigroup (`affine_latin`), even on an infinite
abelian group. The names here are in the namespace `Spectrum.E667.AffineStructure`.

## All medial models and proper submagmas

The follow-up [MedialAffine](../equational_theories/Spectrum/Equation667MedialAffine.lean)
removes the need to assume that an affine presentation is supplied. Every
finite **medial** E667 magma has such a presentation. Here medial means
`(x*y)*(z*w)=(x*z)*(y*w)` for every four inputs. Normalize the two translations
at a point to obtain a loop with identity `a*a`; three instances of mediality
make its left translations commute. This proves commutativity and associativity
of the loop. Subtracting the constant terms from the original translations
then makes them additive maps. This is a direct proof of the relevant Toyoda
representation theorem, including arbitrary diagonal behavior.

`MedialAffine.representation`, `prime_square_dvd`, and
`not_medial_of_mod_nine` are complete Lean proofs. Consequently **any model
at any of the 17 open orders must be nonmedial**. The exclusions at primes
31 and 47 also extend from affine presentations to all medial models.
This does not exclude nonmedial models at those orders.

[SubmagmaBound](../equational_theories/Spectrum/Equation667SubmagmaBound.lean)
proves that an E667 algebra of order n with bijective squaring and a proper
submagma of size m satisfies **3m ≤ n**. If an idempotent lies outside the
submagma, then **3m < n**. In particular the strict bound applies to every
proper submagma of an idempotent E667 algebra. The proof embeds three disjoint
copies of the submagma into the carrier; an outside idempotent is a further
unused point. This is a direct counting proof and assumes no design
representation. The bijective-square hypothesis matters: general E667
algebras can have larger proper submagmas.

Thus a seven-point submagma is impossible inside an idempotent algebra of
order 20, but the bound permits one at 23 or 26. The searches for the latter
two extensions remain inconclusive. These and the other follow-up searches
are recorded in [e667_open_orders_20261004.md](e667_open_orders_20261004.md).

[RegularParity](../equational_theories/Spectrum/Equation667RegularParity.lean)
proves `no_complete_mapping`, `no_regular_model`, and `no_equivariant_model`
at every order 2 modulo 4. Thus a model at 30, 102, or 174 cannot arise from
any regular group of automorphisms. The proof multiplies a sign character
along the two permutations of a complete mapping, obtaining both 1 and -1.
It uses no general Hall–Paige theorem and no finite certificate.

## Verification and remaining boundary

The modules are imported by `equational_theories/Spectrum.lean`. The full
Spectrum target builds. Each major Lean result has a `spectrum_assert ... complete`
check. Existing unrelated spectrum obligations can still contain `sorry`;
none of these new results depends on them.
An explicit axiom audit of the original 43 public results and the nine public
results added in the follow-up found only `propext`,
`Classical.choice`, and `Quot.sound`. The witness metadata's Lean references
and the binary classification generator were also checked.

The remaining hard problem is genuinely nonlinear E667 structure at the
unresolved orders, especially 12 and 15. Neither the group-profile search
exclusions nor the affine decomposition classifies arbitrary E667 magmas.
No website spectrum claim or finite-existence seed changes in this pass.
