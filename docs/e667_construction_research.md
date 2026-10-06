# E667 at 12 and 15: nonlinear constructions and a simplicity obstruction

The quotient and three-element-fiber obstructions below have complete Lean
proofs. The idempotent-free order-five classification and both simplicity
conclusions are now also fully formalized. The full enumeration counts and
construction searches remain separate research computations. Neither order 12 nor 15 is excluded for arbitrary
magmas. The law throughout is

```
x = y * (x * ((x*x) * y)).
```

## Every possible model at 12 or 15 is simple

A finite E667 magma is a quasigroup. Its finite quotients are again E667
quasigroups, and every congruence has equally sized classes: a translation
maps one class injectively into any prescribed target class, and a reverse
translation supplies the opposite inequality. Hence a quotient order divides
the order of the original magma.

Exhaustive enumeration of *all Latin squares*, followed by direct evaluation
of E667, gives the following small classification. This calculation is
independent of the SAT encoding and its symmetry normalization.

| Order | Latin squares tested | E667 tables | Isomorphism classes | Idempotents |
|---:|---:|---:|---:|---|
| 2 | 2 | 2 | 1 | Exactly one in every model |
| 4 | 576 | 16 | 2 | Exactly one in every model |
| 5 | 161280 | 100 | 5 | Four classes have idempotents; one has none |

The unique idempotent-free class at order five is

```
q(i,j) = 3i + 3j + 1  (mod 5).
```

Its squaring map is the five-cycle `i ↦ i+1`. The idempotent-free class has
24 labelled tables; the other 76 tables have idempotents. The exhaustive
classification is recorded in `data/spectrum/667_small_quotients.json` and
reproduced by `scripts/spectrum_667_small_quotients.py`.

`Spectrum/Equation667Quotients.lean` proves uniform fiber cardinalities and
that a congruence class over an idempotent of the quotient is a submagma. Models of
orders 3 and 6 are already excluded in Lean. Consequently a proper quotient
of a hypothetical order-12 model cannot have order 2 or 4 (its idempotent fiber
would have order 6 or 3), and cannot have order 3 or 6 (the quotient itself
would be impossible). **Every order-12 model must therefore be simple.**

At order 15, the only possible nontrivial quotient has order 5, and it must be
idempotent-free. The following short sign argument rules this out too. Thus
**every order-15 model must also be simple.**

The complete order-12 quotient conclusion is now proved in Lean as
`Spectrum.E667.quotient_card_twelve` in `Equation667SimpleTwelve.lean`:
any surjective homomorphism has target order 1 or 12. The two- and four-point
idempotent theorems in `Spectrum/Equation667SmallQuotients.lean` use short
permutation arguments rather than table enumeration. The order-15 conclusion
is now fully proved as `Spectrum.E667.quotient_card_fifteen` in
`Equation667SimpleFifteen.lean`. The idempotent-free five-point classification
is `FiveClassification.exists_iso`, using a 1,458-byte LRAT certificate after
proved row normalization. The general exclusion of the displayed order-five quotient is proved
in Lean as `Spectrum.E667.FiberThree.no_quotient_five`.

### No three-element-fiber extension of the idempotent-free order-five model

Label each fiber by `F₃`. Every Latin square of order three is affine, so a
hypothetical extension necessarily has the form

```
(i,a) * (j,b) = (q(i,j), Aᵢⱼ a + Bᵢⱼ b + Cᵢⱼ),
```

where `Aᵢⱼ,Bᵢⱼ ∈ {+1,-1}` and `Cᵢⱼ ∈ F₃`. The coefficients may vary with
both quotient indices; this is substantially more general than an affine
magma on a single abelian group. Constants cannot affect the following
coefficient obstruction.

For fixed `i,j`, put `s=i+1`, `t=q(s,j)`, and `u=q(i,t)`. Comparing the
coefficients of the two fiber variables in E667 gives

```
Bⱼᵤ (Aᵢₜ + Bᵢₜ Aₛⱼ (Aᵢᵢ+Bᵢᵢ)) = 1,
Aⱼᵤ + Bⱼᵤ Bᵢₜ Bₛⱼ = 0.
```

Write `Dᵢ=Aᵢᵢ Bᵢᵢ`. The first equation forces `Aᵢₜ Bⱼᵤ = -Dᵢ`:
if `Dᵢ=-1`, the parenthesized diagonal sum vanishes; if `Dᵢ=1`, subtracting
two signs can equal `1` in F₃ only as `-1-(+1)`. The second equation says
`Aⱼᵤ Bⱼᵤ Bᵢₜ Bₛⱼ = -1`. These are identities of ordinary signs.

Define products along the five cyclic diagonals:

```
a_d = ∏ᵢ Aᵢ,ᵢ₊d,    b_d = ∏ᵢ Bᵢ,ᵢ₊d,    D = a_0 b_0.
```

All subscripts below are modulo five. Put `j=i+d` and multiply each sign
identity over `i`. Because `t=i+3d+4` and `u=i+4d+3`, the resulting identities
are

```
a_(3d+4) b_(3d+3) = -D,
a_(3d+3) b_(3d+3) b_(3d+4) b_(d-1) = -1.
```

Take the first at `d=1` and the second at `d=3,4`:

```
a_2 b_1 = -D,
a_2 b_3 = -1,
D b_1 b_3 = -1.
```

Multiplying the last two gives `a_2 b_1 = D`, contradicting the first. This
rules out every three-element-fiber extension, without using a large finite
refutation or assuming that the constants vanish. The complete argument,
including the affine form of arbitrary Latin three-point blocks and transport
from an arbitrary fifteen-point carrier, is formalized in
`Spectrum/Equation667FiberThree.lean`.

## Structured searches

The bounded construction probes used principal isotopes `Q(α(x),β(y))` with
arbitrary permutations `α,β`. Up to relabelling, this covers every isotope of
the chosen base quasigroup. The bases include:

- order-12 loops obtained by prolonging affine idempotent quasigroups of order
  11;
- all three nonassociative left Bol loops of order 12 from the GAP LOOPS
  database;
- all 80 Steiner triple systems of order 15 from the same database.

The database source is
<https://github.com/gap-packages/loops/tree/master/data>; the Steiner systems
are attributed there to Colbourn and Rosa, *Triple Systems*. Isotope constraints
are channeled in all three directions between the two permutation entries
and the output entry. Timeouts are recorded as unknown and do not exclude
any family. All 80 Steiner bases reached their 15-second caps without an
answer. The three Bol bases and two prolongation bases likewise timed out at
180 seconds each. A stronger 90-second retry on the Chein loop and a
282-second projective-isotope run with base-automorphism symmetry breaking
also remained unresolved. These outcomes and all 85 base tables are saved in
`data/spectrum/667_nonlinear_isotopes.json`. The reusable driver is
`scripts/spectrum_667_nonlinear_isotopes.py`.

A separate direct exhaustive check ruled out the linear-isotope subfamily of
the projective Steiner quasigroup on `F₂⁴ \ {0}`. Its product is `Q(x,y)=x+y`
for distinct inputs and `Q(x,x)=x`. Testing all pairs `A,B ∈ GL₄(2)` covers
406425600 operations `Q(Ax,By)`; 134865 pass the diagonal instances of E667,
and none passes the full law. This excludes only those linear isotopes,
not arbitrary permutations or arbitrary order-15 magmas.

## A six-instance near miss at order twelve

Permutation annealing on the twelve-point Chein loop produced a Latin square
violating 24 of the 144 E667 instances. Allowing row, column, and symbol cycle
trades, which preserve the Latin property but may change the isotope class,
reduced this to **six** failures. A 300-second run made 291641384 Latin
cycle-trade proposals without improving further. This table is **not an E667 model**.

The failure set is exactly the ordered unequal pairs from `{1,3,5}`. That
three-point core is closed and has the Steiner table

```
1 5 3
5 3 1
3 1 5
```

Every E667 instance with either variable outside the core holds. The first
six points also form a closed subquasigroup, and the two six-point halves give
a two-point quotient. A genuine repair must break these structures: a
three- or six-point E667 submagma is impossible, and a twelve-point E667 model
cannot have the nontrivial quotient just proved impossible.

The explicitly labelled near-models and their failure lists are retained in
`data/spectrum/667_near_models.json`. They are kept separate from the positive
model witnesses. The two search algorithms are
`scripts/spectrum_667_isotope_anneal.cpp` and
`scripts/spectrum_667_latin_anneal.cpp`; returned tables are independently
checked against the original law before any positive claim.

A separate 120-second search among arbitrary isotopes of the projective
Steiner quasigroup at order fifteen reached 42 failed instances. Its table
is also saved as a near-model only. No attempt in this section proves
nonexistence at 12 or 15.

## Reproduction

```sh
python3 scripts/spectrum_667_small_quotients.py
python3 scripts/spectrum_667_nonlinear_isotopes.py leftbol12-1 --seconds 180 --basic
python3 scripts/spectrum_667_nonlinear_isotopes.py gap-steiner15-1 --seconds 300 --pg-lex
c++ -O3 scripts/spectrum_667_projective_linear.cpp -o /tmp/e667-projective-linear
/tmp/e667-projective-linear
```

The nonlinear driver checks any returned SAT witness directly against the
original equation. Its default encoding also adds the newly Lean-proved
square and translation consequences. `--basic` reproduces the earlier
encoding, and `--one-way` additionally reproduces the weaker initial
prolongation-isotope channeling.

## Subsequent order-fifteen restrictions

`e667_mace4_and_order15.md` records the new complete Lean exclusions of
commutative and globally idempotent order-fifteen models, the completed
simplicity proof, and the patient Mace4 experiment. Unrestricted existence
at fifteen remains open.
