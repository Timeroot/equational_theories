# Cofiniteness of E677, E1083, and E1286 by strong block gluing

Effective numerical tails are now available: E677 at 164,475 (now proved in Lean), E1083 at
246,119,111, and E1286 at 4,222,119,949. These are computer-assisted bounds whose
concrete certificates await Lean checking; the cofiniteness results below are
fully proved in Lean. See [E677](e677_effective_bound_20260929.md) and
[E1083/E1286](1083_1286_effective_tails_20260930.md).

28 September 2026; formalization completed 29 September. **All three spectra
are cofinite in Lean.** The proof includes the required design-existence
theorems for block sizes `{5,11,16}` and `{7,9,16}`, as well as the seeds,
gluing, CRT, and residue filling. Their exact spectra and an explicit
numerical cutoff remain open. No finite search timeout is used in the argument.
See [the design proof](wilson_design_formalization_20260929.md) for its structure
and source references.

The new step is to put arbitrary, possibly nonidempotent, models inside the
groups of a transversal design. Strong idempotent models are needed only
on its transversal blocks. This escapes the residue restrictions on the
earlier idempotent constructions.

The identities, with parentheses made explicit, are:

```text
E677:  x = y * (x * ((y * x) * y))
E1083: x = y * ((x * (y * x)) * y)
E1286: x = y * (((x * y) * x) * y)
```

## 1. Strong blocks and arbitrary group fillings

Fix one of the displayed two-variable identities. Call a model **strong**
if it is idempotent and, whenever the original inputs x,y are distinct,
the two arguments at every multiplication node of the identity are distinct.
Strength concerns these particular expressions, not every possible term.

Strong models are closed under products and ordinary PBD gluing. For a
product, a coordinate in which the original inputs differ witnesses each
required inequality. For a PBD, the entire computation for distinct inputs
stays in their unique block, and strength is inherited from that block.

More generally, suppose a group-divisible design has strong models on its
transversal blocks and arbitrary models on its groups. For two points in
the same group, use its group operation. For points in different groups,
use the operation of their unique transversal block. An identity instance
whose inputs lie in one group stays there. Otherwise, compute it first
in their transversal block. Its multiplication arguments are always
distinct block points, hence belong to distinct groups. The global operation
therefore agrees with the block operation at every node, proving the identity.
**The groups need not be idempotent.**

In particular, truncate one group of TD(k+1,q) to r points, 0<r≤q.
Its remaining blocks have sizes k or k+1. Strong models of these two sizes,
together with arbitrary models of sizes q and r, give a model of order

    kq+r.

This is the essential difference from the earlier idempotent PBD closure.

## 2. A general residue-filling argument

Let p be prime. Suppose an identity has:

1. strong models at every sufficiently large order congruent to 0 or 1 mod p;
2. strong models at k and k+1, where p divides k;
3. for each other nonzero residue a mod p, a model at a prime order g_a
   congruent to a, with g_a≤k and gcd(g_a,k)=1.

Then its spectrum is cofinite. Here is a constructive reduction to the
threshold in assumption 1; no general asymptotic theorem about transversal
designs or primes in progressions is needed.

Take C≥k+1 such that assumption 1 holds for n≥C. Let

    M = product of all primes at most k.

Fix a missing residue a and write g=g_a. Choose e with g^e≥k, and put
D=g^e M. Consider any sufficiently large n≡g (mod p).

If g does not divide n, use the Chinese remainder theorem to choose q in
the progression specified by

    q ≡ n*k⁻¹ (mod g),
    q ≡ 1 (mod every other prime at most k).

Every such q is coprime to M and is 1 mod p. Its progression has step M≤D.

If g divides n, instead put q=g^e Q, where CRT specifies

    Q ≡ (g^e)⁻¹ (mod p),
    Q ≡ 1 (mod every other prime at most k).

Then Q is coprime to M, q≡1 (mod p), and q is divisible by g. This progression
for q has step D. In both cases select its first q≥n/(k+1). Thus

    n/(k+1) ≤ q < n/(k+1)+D.

Every maximal prime-power factor of q is at least k: in the first case all
its prime factors exceed k; in the second, the exceptional factor is g^e.
A field of order s supplies TD(s+1,s), so restricting groups and taking
products supplies TD(k+1,q).

Put r=n−kq. The congruences ensure g divides r. Also

    r≤q,       r>n/(k+1)−kD.

For n≥(k+1)(gC+kD), both q≥C and t=r/g≥C. Since p divides k and
n≡g (mod p), t≡1 (mod p). Assumption 1 supplies strong models at q and t.
The product of the g-model and the t-model supplies the possibly
nonidempotent r-model. Section 1 now constructs the required n-model.

Take the maximum of these bounds over the finitely many missing residues.
Orders 0 and 1 mod p were already covered by assumption 1. This proves
cofiniteness for all residue classes.

## 3. Strong affine and companion seeds

For an idempotent affine operation x*y=(1-b)x+by over a field, a term
evaluates as u*x+(1-u)*y. Two subterms differ on distinct inputs exactly
when their x-coefficients differ. The following table gives the polynomial
f(b) required for the law and the coefficient differences at all four
multiplication nodes, listed from the outermost node inward:

| Law | f(b) | Node differences |
| --- | --- | --- |
| E677 | b⁴−b³+b²−b+1 | (b−1)(b²+1), b²−b+1, b, −1 |
| E1083 | b⁴−2b³+2b²−b+1 | (b−1)(b²−b+1), b²−b+1, 1−b, −1 |
| E1286 | b⁴−2b³+2b²−b+1 | (b−1)(b²−b+1), b²−b+1, −b, 1 |

For every listed difference d, the resultant Res(f,d) is 1. Consequently
f and d generate the unit ideal in Z[b]; any root of f in any field makes
d nonzero. This verifies strength as well as the law. Equivalently, the
Bezout identities make d(T) invertible for the companion operator T of f
over any commutative ring. Thus the existing fourth-power companion models
are strong too. The accompanying checker records integral Bezout identities.

All finite-field coefficient data below use the polynomial bases already
specified in `data/spectrum/open_survey_20260927.json`. The checker verifies
the field arithmetic, law coefficients, and all four strict inequalities.

## 4. Application to E677

Strong seeds have sizes 5,11,16. Wilson's PBD theorem gives strong models
at every sufficiently large order 0 or 1 mod 5, because the two design gcds are

    gcd(4,10,15)=1,      gcd(20,110,240)=10.

Take k=80. A product of the strong 5- and 16-models gives the strong
80-model, and the fourth-power companion gives the strong 81-model.
The missing residues have these prime models, all checked directly:

| Order g | Operation modulo g | g mod 5 |
| --- | --- | --- |
| 7 | 4x+y | 2 |
| 13 | 9x+11y | 3 |
| 19 | 7x+3y | 4 |

They are nonidempotent; this was precisely what prevented their use in
ordinary PBD gluing. Each is coprime to 80. Section 2 proves cofiniteness.
For example, e=3,2,2 suffice for g=7,13,19. A common bound, expressed in
terms of the Wilson threshold C, is

    81*(19*C + 80*361*M),
    M=3217644767340672907899084554130.

This is not a numerical cutoff, because the argument has not supplied a
numerical value of C.

There are also explicit new construction families independent of Wilson:
TD(81,q) with a strong q-model and r∈{7,13,19} gives 80q+r.
Taking q=81 yields orders **6487,6493,6499**, one in each missing residue.
Taking q=m⁴ gives the same three families whenever all maximal prime-power
factors of m⁴ are at least 80; in particular for odd m≥3, or m divisible by 4.

These constructions do **not** refute E677→E255. Each diagonal computation
stays in a group, and all group fillings used here satisfy E255.

## 5. Applications to E1083 and E1286

Both identities have strong seeds of orders 7,9,16 with the same operations.
Wilson gives every sufficiently large order 0 or 1 mod 3, since

    gcd(6,8,15)=1,       gcd(42,72,240)=6.

Take k=1008=7*9*16. Products give its strong model for both identities.
For k+1=1009, the prime-field operation

    x*y = 958*x + 52*y (mod 1009)

satisfies both identities and is strong: 52 is a root of the shared quartic.
The remaining residue is represented by g=11, coprime to 1008:

* E1083: x*y=6x+9y (mod 11);
* E1286: x*y=x+7y (mod 11).

Section 2 proves cofiniteness of both spectra. With M the product of primes
at most 1008, e=3 gives the bound

    1009*(11*C + 1008*1331*M).

Again this depends on the currently nonnumerical Wilson threshold C.
The explicit construction with q=1009 and r=11 gives order **1017083**
for each law. More generally, 1008q+11 is obtained whenever q≥1008 has
a strong model and TD(1009,q); fourth powers of primes at least 7 suffice.

## Status, verification, and remaining work

The original paper argument invokes Wilson's PBD existence theorem:
R. M. Wilson, *An existence theory for pairwise balanced designs III*,
J. Combin. Theory Ser. A 18 (1975), 71–79,
https://doi.org/10.1016/0097-3165(75)90067-9.
The use of this theorem was already justified for the restricted residues;
the new group-filling argument fills the remaining ones.

The gluing theorems and explicit finite witnesses for all three laws are now
formalized in Lean. The E1083/E1286 work also supplies new common-point
polynomial families; see `docs/1083_1286_common_point_20260929.md`.
The cofiniteness reductions, including CRT, and both design-existence
instances are now fully formalized. The new design library follows the
eventual-periodicity argument in Wilson's 1969 thesis, using prime-power
affine seeds in place of the general uniform-design existence input.
The accompanying scripts verify the finite seeds, strength and polynomial
identities, CRT conditions, and explicit finite gluing examples. These checks
support the argument; they do not replace the proof or a Lean formalization.
E907's even orders and the E1483 spectrum are not settled by this method.
E670 was already known cofinite on paper and still needs an explicit tail
or a formalization of the relevant design existence result.

The exhaustive checker constructed the three E677 tables in memory and
verified all **126,477,219** ordered pairs. Each model has exactly 6481
idempotents, and E255 holds at every point. The tables are discarded;
the saved recipes, input hashes, and value-sequence checksums reproduce them.
Run `python3 scripts/spectrum_strong_gluing.py --exhaustive` to repeat this
check, or omit `--exhaustive` for the seed, Bezout, and CRT checks.
The full verification record is `data/spectrum/strong_design_cofiniteness.json`.

The catalogue records all three cofiniteness results as `PROVED`.
`Spectrum.Pending.cofinite_677`, `Spectrum.Pending.cofinite_1083`, and
`Spectrum.Pending.cofinite_1286` have only the standard Lean axioms in their
transitive dependencies. The finite witnesses and infinite construction
families remain separately recorded; no numerical cutoff is inferred.

## Lean formalization of the cofiniteness reduction (29 September)

The following modules contain no `sorry` and do not import `NotePending`:

* `PBD/Cyclic.lean` constructs TD(k+1,q) whenever q is coprime to the product
  of primes at most k. The proof uses units of Z/q and finite slopes.
* `PBD/ResidueFilling.lean` proves the CRT progression and the decomposition
  n=kq+gt, with q,t in residue one and gt≤q. When g divides n, a finite-field
  factor g^e is combined with a cyclic design on the coprime quotient.
* `PBD/Existence.lean` defines a finite PBD, glues arbitrary idempotent binary
  law models along its blocks, and verifies both design gcd conditions for
  `{5,11,16}` and `{7,9,16}`. `WilsonExistence` is a proposition, not an axiom.
* `Equation677/Cofiniteness.lean` proves `Spectrum.E677.cofinite_of_wilson`.
* `Equation1083_1286/Cofiniteness.lean` proves the shared
  `Spectrum.E1083E1286.cofinite_of_wilson` for both laws.

The last two statements take the specified Wilson instance as an explicit
hypothesis. Their transitive axioms are only `propext`, `Classical.choice`,
and `Quot.sound`. They also prove the stronger reduction from an arbitrary
model tail in residues zero and one: those tail models need not be idempotent.

For simpler uniform arithmetic the Lean proof uses e=4 for all exceptional
primes. With M the product of primes at most k, its sufficient bound for
one missing residue is

    (k+1) * (g*C + 2*k*(g^4*M) + C + 1).

Take the maximum with 1, C, and the bounds for the other missing residues.
This is larger than the earlier paper estimate, but equally sufficient.
It is still not a numerical cutoff because C is the unknown Wilson threshold.

**Completed design obligations:** `PBD/WilsonInstances.lean` proves
`Spectrum.PBD.wilson_5_11_16` and `Spectrum.PBD.wilson_7_9_16`.
The compatibility declarations in `NotePending.lean` now apply these proofs.
Both concrete instances include checked axiom reports excluding `sorryAx`.
The remaining work for these spectra is to obtain a useful numerical cutoff
and classify the smaller orders.

### Attempt to replace the Wilson input by a finite construction (29 September)

This earlier attempt did not discharge the design obligations; the general
proof above subsequently did. The search
is saved as `scripts/spectrum_677_tail_closure.cpp`. It starts with every
idempotent finite-field E677 order within a chosen bound and closes under
products, the 80/81 one-hole construction, and common-point constructions.
The field criterion is explicit: for p≠5 a primitive fifth root in F_(p^e)
gives the required root of Φ10, so 5 divides p^e−1; characteristic 5 uses
the scalar seed. Products combine the primary factors. Designs are used
only when every maximal prime-power factor of the group order is large
enough. All these are positive construction rules; a missing mark says
nothing about nonexistence.

At bound 30,000,000 the search still misses 1,362,184 admissible orders
between 10,000,000 and 30,000,000. It marks every tested order congruent to
1 modulo 10 above 3,795,191, but a finite interval does not establish a tail.
This search is external research evidence, not a Lean certificate, and it
does not change any catalogue status. No large bitmap is stored in the repo.

There is a smaller elementary design-order gap bound which could help a
future finite-certificate approach. Among 33 consecutive terms of an
arithmetic progression of step 30, the primes 7 through 79 can exclude at
most `sum(ceil(33/p)) = 32` terms. Taking the progression 1 mod 30 therefore
finds an order coprime to the 80-primorial within a gap of 990. Likewise,
1202 consecutive terms of step 2310 suffice for the 1008-primorial: the
primes 13 through 997 exclude at most 1201 terms, giving gap 2,776,620.
These counting bounds are paper arguments, not new Lean theorems. They
reduce the arithmetic cost but do not supply the missing initial design
interval or prove Wilson's theorem.

Reproduce the bounded search by compiling the C++ file with `g++ -O3
-std=c++17` and running the executable with argument `30000000`. An optional
second argument writes its research bitmap; the default retains only the
printed summary.

## Symbolic Lean formalization of the E677 witnesses

The Lean proofs use compact construction data, not the expanded tables:

* The 5-point block has operation `2x+4y` over `ZMod 5`.
* The 16- and 81-point blocks use the existing four-coordinate companion
  operation over `ZMod 2` and `ZMod 3`, respectively. Its law and idempotence
  are polynomial identities already proved over arbitrary commutative rings.
* The 80-point block is the product of the 5- and 16-point blocks.
* A field of order 81 supplies the transversal design. Its pair-covering
  property follows from field algebra, rather than enumeration of lines.
* Truncating the last group to 7, 13, or 19 points and filling it with
  `4x+y`, `9x+11y`, or `7x+3y` gives the three claimed orders.

There is a useful strengthening of the paper's affine strength check:
**every finite idempotent E677 model is strong.** Each left translation is
surjective by E677 and hence injective. Therefore `y*x=y` implies `x=y`.
If `(y*x)*y=x`, the law first gives `y*x=x`, hence also `x*y=x`; the law
with the inputs swapped then forces `x=y`. Finally, if
`x*((y*x)*y)=y`, the original law and idempotence again force `x=y`.
These are precisely the three nontrivial intermediate inequalities.

`Equation677/Gluing.lean` proves this argument and the group-divisible
gluing theorem. `Equation677/DesignModels.lean` proves the truncation and
cardinality calculation. `Equation677/DesignWitnesses.lean` supplies the
seed formulas and proves `Spectrum.E677.model6487`, `model6493`, and
`model6499`, all without `sorry` or native-computation axioms. The only
closed numerical seed checks are two modular coefficients per affine model
(and idempotence for the 5-point seed), not all pairs of elements.

The compact recipe is also recorded in
`data/spectrum/677_design_models.json`. Finite relabellings in the Lean
construction need not reproduce the numerical labels of the earlier C++
tables; the Lean proof constructs the stated cardinalities directly.
