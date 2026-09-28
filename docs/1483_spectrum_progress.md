# E1483: constant rows, cubic untwisting, and small orders

26 September 2026. The general spectrum remains open. All squares and twice
squares occur. This pass proves a complete cardinality restriction for the
constant-row subclass, excludes order ten, and upgrades the order-seven
exclusion to a complete Lean proof. Both finite exclusions use checked LRAT
certificates.

## Constant rows force power-of-two cardinality

Suppose a magma satisfies

```
(y*x) * (x*(y*z)) = x
```

and has a constant row `0*x=1`. Write `N(x)=1*x` and `φ=N²`. The previously
proved constant-row identities give `N⁶=id`, and show that φ preserves
multiplication. Thus φ is an automorphism with `φ³=id`. They also give

```
1*(x*1)=x,  (1*x)*1=x,  x*0=1,
1*1=0,     1*0=1,      φ(0)=0,  φ(1)=1.
```

There are two new equational conclusions:

1. `φ(x)*y = φ(y)*x`.
2. The operation `B(x,y)=φ²(x)*φ(y)` satisfies E1485.

Both have complete equational proofs, now replayed in Lean using ordinary
equality rewriting. The second also follows conceptually from the first:
because φ is an automorphism of order three,

```
B(B(y,x),B(x,B(z,y)))
  = (φ(y)*x) * (x*(φ(z)*y))
  = (φ(y)*x) * (x*(φ(y)*z))
  = x.
```

The first identity makes B commutative as well. Its row at 0 is still constant:
`B(0,x)=1`. The E1485 degree theorem says that a finite model has order
`r²·2^k`, where r is its minimum row rank. Here r=1. Consequently:

**Every finite E1483 magma with a constant row has order `2^k`.**

Conversely, pointwise Boolean NAND on the k-dimensional Boolean cube satisfies
E1483 and has a constant row, so every `2^k` occurs in this subclass. No
nontriviality assumption is needed; k=0 gives the singleton magma.

A bijective row in an E1483 magma supplies a constant row, by the existing
`CentralConstant.bijective_row_gives_constant` theorem. Hence the same
power-of-two restriction applies when any row is bijective.

The algebraic untwisting works on infinite carriers too. The power-of-two
cardinality conclusion uses finiteness through the E1485 degree theorem.
This does not assert that every E1483 magma has a constant row, or that the
general E1483 spectrum consists only of powers of two.

## Lean sources

- `Spectrum/Equation1483/ConstantBasic.lean`: inverse translations, uniqueness
  of the constant row, and the automorphism φ.
- `Spectrum/Equation1483/ConstantUntwist.lean`: the two equational proof
  replays; both have empty axiom lists.
- `Spectrum/Equation1483/ConstantSpectrum.lean`: the E1485 operation and
  `card_pow_two`, `card_pow_two_of_bijective`, and the exact subclass
  characterization `exists_constant_iff`. These use only `propext`,
  `Classical.choice`, and `Quot.sound`.

Reproduce the equational replay with `python3 scripts/spectrum_1483_constant.py`.
The saved traces are in `data/spectrum/1483_constant_untwist_proofs.json`.

## Small-order searches

At an order that is not a power of two, every row has rank between 2 and n−1.
Relabel a minimum-rank row as row zero, normalize its image to an initial
segment with or without zero, and sort the remaining input labels by that
row's outputs. The existing row/column rank and edge-product bounds are
necessary conditions, all proved in Lean independently of the searches.

At order ten, all eight minimum-rank cases 2 through 9 returned UNSAT. The
respective elapsed times were approximately 14.7, 32.3, 51.4, 4.7, 0.54, 0.24,
0.20, and 0.18 seconds. Together with the constant-row theorem this gives a
complete external nonexistence argument. The fourteen normalized cases have
now all been replayed in Lean, and `Spectrum.not_order_1483_10` passes the
complete proof-status audit. The certificate bundle totals about 73 MiB compressed;
the original order-eleven certificates remain separate and are not required.

Order seven has also been completed in Lean, as `Spectrum.not_order_1483_7`.
Its nine normalized cases cover rank 2 with zero absent from the first-row
image, and ranks 3 through 6 with zero either present or absent. The compressed
certificates total 375,163 bytes. This replaces the former admitted
order-seven obligation; it introduces no new admission.

For both orders, every Python-generated CNF was compared byte for byte with
the corresponding formula exported by Lean (23 cases altogether). The Lean
normalization and encoding-soundness proofs reduce an arbitrary hypothetical
model to these cases. Lean's registered native LRAT checker then verifies each
refutation. The aggregate theorems pass `spectrum_assert ... complete`.
The generators and certificate audits are
`scripts/spectrum_1483_{seven,ten}.py` and
`scripts/spectrum_1483_{seven,ten}_certificates.py`.

At order twelve, the first 90-second-per-case pass refuted ranks 6 through 11;
ranks 2 through 5 were inconclusive. A complete 40-case partition of normalized
rank-two first rows refuted all 36 unbalanced profiles within 45 seconds per
profile. The four balanced profiles, each containing six copies of each
output, were then refuted in 148–168 seconds each after adding the already
proved fiber-injectivity constraints. Thus the entire minimum-rank-two case
is excluded externally. These are external search results, not Lean exclusion
certificates. A separate 900-second run for each of ranks 2, 3, 4 and 5 was
inconclusive; the successful rank-two partition supersedes that unsplit run.
Ranks 3, 4 and 5 remain the possible minimum ranks of an order-twelve model.
A further complete partition of rank-three cases by the normalized four-entry
first-row prefix had 18 cases. With collision constraints and 120 seconds per
case, six were refuted and twelve were inconclusive.
No order-twelve nonexistence conclusion follows from these partial results.

The new order-ten exclusion does not by itself close an additional pending
finite FO-definability comparison into E1483. The current reduced inventory
has only E1485 and E1486 as unresolved sources for that target: E1485 excludes
ten already, and existence at ten is still unknown for E1486.

## Equality in an edge bound gives exact coordinates

Suppose `b` lies in row `a`, and `|G|=r(a)r(b)`. The existing injection

```
x ↦ (a*x, x*b) ∈ Row(a) × Col(b)
```

has source and target of the same finite cardinality, so it is bijective.
E1483 makes multiplication its inverse. Consequently, for every `u` in row a
and `v` in column b,

```
a*(u*v)=u,    (u*v)*b=v.
```

Translation regularity then gives the two sharp-edge identities
`a*(b*x)=b` and `(x*a)*b=a`. Every nonempty fiber of row a has size r(b).
This proves uniformity at a saturated edge, without assuming that all edges
are saturated or that sharp neighbors always exist.

These statements are formalized in
`Spectrum/Equation1483/SharpCoordinates.lean`: `coordinates_bijective`,
`coordinates_multiply`, `sharp_left`, `sharp_right`, `leftFiberEquiv`, and
`fiber_card_left`. They use only the standard logical axioms. Together with
`RankRigidity.central_of_uniform_square`, they isolate the equality cases of
the currently proved counting bounds.

The converse, obtaining exact rectangular coordinates from a sharp edge
without assuming equality in the rank bound, remains unproved in this pass.
Three equational searches for the dual sharp identity and the two coordinate
identities each reached their 180-second caps. Their inputs and logs are
included in the search archive; they supply no additional theorem.

## Projectors and the remaining structural obstacle

For fixed a, put `P_b(t)=a*(t*b)`. In the checked examples these satisfy
`P_b²=P_b` and `P_b P_c P_b=P_c P_b`. The general identities remain unproved.
The second identity would allow a finite family to acquire a common fixed
point by successive application. It is weaker than commutativity: the saved
nine-element model and a new eight-element model refute commutativity of these
maps, including a counterexample on the image of the row at a.

The known eight-element constant-row example becomes E1485 after cubic
untwisting. The two previously saved nine-element examples already satisfy
the central groupoid law E168. These examples are therefore weak evidence for
the unproved projection identities; they do not yet test a model outside the
E1485/cubic-twist construction.

It is tempting to conjecture that all E1483 models are cubic automorphic
twists of E1485 models. That is a research direction, not a proved
representation theorem or an established spectrum classification.

The subsequent [rank-descent investigation](1483_rank_descent_followup.md)
found an eight-element counterexample to a proposed retraction between row
images. The counterexample itself is checked by Lean's kernel in
`RetractionCounterexample.lean`. It refutes that proposed proof, not the
rank-descent conjecture. A corrected route is reduced to two explicit open
identities, absorption and collapse; neither is used in the completed results.

The [general-construction pass](1483_general_constructions.md) adds Lean-checked
permutation constructions, including nonnatural central groupoids and extensions
of arbitrary E1483 bases, and a weighted-cover construction. It also proves in
Lean that every group-affine E1483 operation satisfies E168, even over
nonabelian groups. A separate complete pen-and-paper argument rules out the
natural projective-plane correlation construction. No new spectrum order is
claimed by that pass; its restricted searches and positive examples are saved
separately from the spectrum catalogue.

## Reproduction

```sh
python3 scripts/spectrum_1483_constant.py
python3 scripts/spectrum_1483_seven.py
python3 scripts/spectrum_1483_ten.py
python3 scripts/spectrum_1483_seven_certificates.py
python3 scripts/spectrum_1483_ten_certificates.py
python3 scripts/spectrum_1483_search_check.py
python3 scripts/spectrum_1483_projector_check.py
python3 scripts/spectrum_1483_rank_descent_check.py
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
python3 scripts/spectrum_generate.py --check
```

The [saved searches](../data/spectrum/1483_search_followup.json) distinguish
UNSAT solver reports from inconclusive runs and include the full positive
table found at order eight. The [source archive](../data/spectrum/1483_search_sources.tar.gz)
preserves the exact search wrappers, time limits, inputs, and logs. Its checker
verifies the archived hashes, case coverage, and positive table directly; it
does not certify the exploratory UNSAT results.

Final verification on 26 September: the full spectrum build passed, followed
by `scripts/check_spectrum.lean`. That audit checked all 4,694 laws and every
catalogue declaration's type and transitive proof dependencies. The new E1483
upper bound is complete; the general E1483 spectrum remains mathematically
open. All certificate and research-data checks above passed as well.
