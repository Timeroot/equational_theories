# E907 and the even-order question — 30 September 2026

The general question remains open: **can a finite E907 magma have even order?**
No even-order model was found in this investigation. The smallest open even
order remains **10**. The new universal results below are proved in Lean;
the bounded searches and construction-family checks are recorded separately.

## Completed spectrum facts

The earlier requested formalizations are complete:

- `Spectrum.E907.eventually_odd` in `Spectrum/Equation907/OddTail.lean`
  proves that every sufficiently large odd order has a model. The stronger
  `eventually_odd_idempotent` retains idempotence. Seeds of orders **3 and 23**
  suffice: the constructive design periods 6 and 506 have gcd 2, and the
  singleton fills the odd residue class. There is no extracted numerical cutoff.
- `Spectrum.not_order_907_8` in `Spectrum/Equation907Eight.lean` excludes every
  order-8 magma, using normalization of the first row and 45 checked finite
  refutations. This uses the repository's registered native-computation policy.
  The external SAT solver is not an axiom of this proof.

The proved excluded orders are **2, 4, 5, 6, 8**. The odd tail and the exclusion
of 8 are also transferred to the dual law E2700 in the checked catalogue.

## New Lean theorem: all finite group-affine models have odd order

Consider an arbitrary finite group, arbitrary endomorphisms `f,g`, and an
arbitrary constant `c`, with operation

    x * y = f(x) g(y) c.

If this operation satisfies E907, then:

1. Both endomorphisms are automorphisms.
2. The underlying group is abelian.
3. Its cardinality is odd.

Thus this rules out nonabelian group constructions of this form as well as
abelian affine constructions, without assuming commuting coefficients or a
zero constant. This theorem does not cover arbitrary quasigroups or arbitrary
isotopes of groups obtained using permutations that are not endomorphisms.

The proof first obtains surjectivity of `g` from the left translations. The
identity with first argument the group identity shows that the kernel of `f`
is trivial; finiteness makes both maps invertible. The identity with second
argument the group identity, after absorbing the constants by conjugation,
then has the form `alpha(x) beta(x) = x` for two automorphisms. Applying it to
`xy` in two ways shows that every element in the image of `alpha` commutes
with every element in the image of `beta`. Surjectivity makes the group abelian.

In additive notation, expanding E907 for `Ax + By + c` gives the endomorphism
identities

    B(AB + BA) = I,          A + BA² + B³ = 0.

Put `C = B⁻¹`, so `AB + BA = C` and `A² + CA + B² = 0`. A useful strengthening
of the earlier characteristic-two obstruction is that these identities force
**A and B to commute over every unital ring**. For `D = AB - BA`, the two
relations give

    DB = D,  BD = -D,  DC = D,  CD = -D,
    AD = DA,  2AD = D,  3D = 0,  7D = 0.

The last two equations imply `D=0`. Therefore `2BAB=I`: doubling has a left
inverse on the underlying additive group. There is no nonzero element of
order two, so Cauchy's theorem gives odd cardinality. This entire calculation,
including the noncommutative ring argument and the group reduction, is checked
in Lean with only `propext`, `Classical.choice`, and `Quot.sound`.

Sources:

- `Spectrum/Equation907/Affine.lean`: `E907.Affine.coefficients_commute`,
  `E907.Affine.commute`, and `E907.Affine.odd_card`.
- `Spectrum/Equation907/GroupAffine.lean`:
  `E907.GroupAffine.coefficients_bijective`, `commutative`, and `odd_card`.

## New Lean theorem: no pointed cycles of lengths two, three, or four

Write `L_a(x)=a*x`. In every finite E907 model,

    L_a²(a)=a, L_a³(a)=a, or L_a⁴(a)=a  implies  a*a=a.

Hence the cycle of `a` under `L_a` is either a fixed point or has length at
least five. This statement concerns the cycle containing `a`; other cycles
of `L_a` may have lengths two, three, or four.

The proof uses left cancellation and the term expression for inverse left
translation:

    (a*(a*x))*((a*x)*a) = x.

For example, in the four-step case put `s=a*a`, `t=a*s`, and `u=a*t`, with
`a*u=a`. The inverse identity and cancellation successively give `u*a=s`,
`t*a=a`, and `s*a=a`. E907 applied to `(a,u)` then gives `a=s`.
The other two cases are similarly short. Vampire discovered the identities;
the Lean proofs are direct equational arguments and do not trust an ATP answer.

Source: `Spectrum/Equation907/PointedCycles.lean`,
`E907.pointed_period_two`, `pointed_period_three`, and `pointed_period_four`.

These facts explain exactly the 48 easy cases among the 97 canonical first
rows at order 10: they are the rows whose cycle containing zero has length
2, 3, or 4. The other 49 forms remain possible. The row-search tool can now
add these proved constraints for **every** row with `--short-cycles`.

The baseline run lasted about 20 minutes and the strengthened run about
10.6 minutes. Both tried all 97 forms at 10,000 conflicts, then revisited
23 and 13 unresolved forms respectively at 200,000 conflicts before their
time budgets expired. Neither reached the scheduled million-conflict phase.
Both finished with the same 48 excluded and 49 unresolved forms; neither
constitutes a nonexistence proof at order 10.

## Structural hypotheses investigated but not proved

The law forces finite left cancellation. Right cancellation is still unknown.
The following possible routes were tested with Vampire, with explicit inverse
left-translation identities, and in some runs with both quasigroup divisions:

- Right cancellation and injectivity of the squaring map.
- Squaring as an endomorphism.
- The candidate idempotent term `(x*x)*x` and existence of an idempotent.
- In the idempotent subclass, flexibility and symmetry of
  `t(x,y)=y*(y*(x*y))`. If a finite quasigroup admitted this symmetric
  idempotent operation, it would provide a route to odd cardinality: for fixed
  `y`, this is a composition of permutations of `x`, so symmetry would make
  `t` a commutative idempotent quasigroup. Each symbol then occurs once on the
  diagonal and in pairs off the diagonal, forcing odd cardinality.

The general ATP runs timed out after 60–300 seconds per target. SAT probes
refuted failures of right cancellation, injective squaring, the proposed
idempotent term, and existence of idempotents at order 7; those are external
small-order results, not proofs of the general hypotheses. Probes at orders
9 and 11 were inconclusive at 200,000 conflicts. Tests of midpoint symmetry
in idempotent models, both with and without right cancellation, were
inconclusive at orders 9 and 13 with 500,000 conflicts.

One stronger guess was actually false: `L_x³(y)=L_(x*x)(y)` fails in the
E907 model `x*y=4x+y` on Z/7 at `x=1,y=0`. The two sides are 5 and 6.
It is not used in any proof.

## Nonlinear construction searches

### One-point prolongations

A transversal in a quasigroup table selects cells `(x,pi(x))` with pairwise
distinct columns and outputs `sigma(x)`. The standard prolongation replaces
those outputs by a new point `infinity` and sets

    x*infinity = sigma(x),
    infinity*pi(x) = sigma(x),
    infinity*infinity = infinity.

This gives an even-order quasigroup from an odd-order one, so it is a natural
way to look beyond affine constructions. All transversals were enumerated in
nine concrete E907 seeds: the order-3 model; a nonidempotent scalar model and
the Steiner model at 7; two F9 models; and both scalar models at 11 and 13.
**All 2,141,117 prolongations failed E907**, already on pairs involving the
new point. This includes complete checks of these constructions aimed at
orders 10, 12, and 14. It is not an exclusion of arbitrary models at those orders.
The seed tables and individual counts are saved with the research data.

The counts at orders 3 and 7 were independently checked by Python permutation
enumeration. A general theorem forbidding prolongations was also attempted,
but the corresponding ATP runs timed out; no such theorem is claimed.

### Group constructions with inversion

The proved group-endomorphism theorem does not automatically cover the forms

    x*y = f(x)^epsilon g(y)^delta c,

where `epsilon,delta` are independently +1 or -1, with at least one -1, and
`f,g` are group automorphisms. These were therefore searched separately.
The search exhausted **16,450,848 candidates**, with every automorphism and
constant, over the dihedral groups of orders 10,12,14,16,18,20,24,30,32,60,
and over A4, S4, and A5. None satisfied E907. All were rejected already by
pairs in which one argument is the group identity. An order-3 positive
sanity check recovered and independently verified the Steiner operation.
These finite construction-family exclusions are external computations,
not Lean proofs or exclusions of arbitrary E907 magmas of those orders.

## Remaining obstruction and reproduction

Products and ordinary design gluing of known odd-order ingredients cannot
supply the first even model. In a PBD whose blocks all have odd size, the
blocks through a point partition its other `n-1` points into sets of even
size, forcing `n` odd. Likewise, an extension with a two-element fibre over
an idempotent quotient element would contain an impossible order-2 submodel.
These observations constrain construction strategies but leave general
noncommutative, non-group-affine models unresolved.

Research data: `data/spectrum/907_even_research_20260930.json`.
The full group tables and automorphism lists for the inversion search are in
`data/spectrum/907_group_inputs_20260930.json`.

```sh
# General finite-model searches; UNKNOWN is preserved on budget exhaustion.
python3 scripts/spectrum_907_row_search.py 10 --seconds 1200 \
  --budgets 10000 200000 1000000 --output /tmp/e907-ten.json
python3 scripts/spectrum_907_row_search.py 10 --short-cycles --seconds 600 \
  --budgets 10000 200000 1000000 --output /tmp/e907-ten-short-cycles.json

# Counterexample probes for named structural hypotheses.
python3 scripts/spectrum_907_parity_probes.py 7 9 11 \
  --properties right_incident right_nonincident square idempotent_term no_idempotent \
  --budget 200000 --output /tmp/e907-structure.json

# Construction-family enumerators: input formats are documented in each file.
g++ -O3 -std=c++17 scripts/spectrum_907_prolongations.cpp -o /tmp/e907-prolongations
g++ -O3 -std=c++17 scripts/spectrum_907_group_search.cpp -o /tmp/e907-group-search

LEAN_NUM_THREADS=4 lake build equational_theories.Spectrum
LEAN_NUM_THREADS=4 lake env lean scripts/check_spectrum.lean
```

The full spectrum build passed (3,985 jobs). The catalogue audit verified all
4,694 laws, including the odd tail and the order-8 exclusion. All new structural
proofs pass `spectrum_assert ... complete`; no new `sorry` or axioms were added.
The catalogue generator, finite-proof generator, and 18 overview tests passed.
The deployment bundle has not been regenerated, and no commit was requested.
