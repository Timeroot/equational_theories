# E704 to E467: inverse profiles and a product constraint

28 September 2026. Follow-up to `fo_704_467_research.md`.
The finite FO direction E704 → E467 and the E467 spectrum cell at 47
remain open. This pass adds a reusable Lean theorem and a stronger bounded
search formulation, not a new spectrum exclusion or FO negative.

## Inverse-row normalization

Let a homogeneous E467 operation on a finite field have

```
p(0,y) = c*y,      p(x,y) = x*f(y/x) (x ≠ 0),      f(1) = s.
```

The finite E467 quasigroup properties imply that `f` has an inverse `g`,
that `c`, `s`, and `f(0)` are nonzero, and that the right profile

```
H(0) = c,         H(t) = f(t)/t (t ≠ 0)
```

is also a permutation. Applying E467 at `(1,t)`, `(0,1)`, and `(1,0)` gives

```
f(f(t)) = (t/s)*g(s/t)    (t ≠ 0),
g(0) = c²*s,
c*f(f(0)) = 1.
```

The diagonal identities already recorded in the earlier note give
`f(s)=1/s` and `f(s²)=s²`. The new encoding uses `AddInverse(f,g)` and
the first formula, avoiding the previous three nested lookup operations.

## A general product theorem, proved in Lean

For any two permutation profiles `f,H` of this shape over any finite field,
let `b` be the nonzero position of zero in `f`. Then

```
f(0) = -c*b.
```

To prove this, put `P=∏_{t≠0,b} f(t)` and `Q=∏_{t≠0,b}t`.
The product of all nonzero field elements is −1, and the two permutations
give

```
f(0)*P = -1,       b*Q = -1,       c*P/Q = -1.
```

Since `Q≠0`, elimination gives the claim. The argument also works in
characteristic two; no odd-characteristic assumption is necessary.

`Definability/HomogeneousQuasigroupProduct.lean` formalizes both this
calculation and its profile hypotheses. The principal public theorem is
`Definability.HomogeneousQuasigroup.zero_product_of_profiles`.
Its axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

Consequently E467 has the additional constraint `f(0)=−c³s`.
For the E1516 normalization, where `g(0)=c²/s`, the corresponding constraint
is `f(0)=−c³/s`. This corollary is formalized separately in
`Definability/Homogeneous1516/ProductConstraint.lean`, as
`Definability.Homogeneous1516.Normalized.zero_eq_neg_cube_div`, with the
same standard-three-axiom audit. The generic theorem applies to other
homogeneous quasigroup searches as well.

## Bounded order-47 probes

The source `4x+20y` satisfies E704 over F47. On F47², a definable E467
companion must be GL(2,47)-equivariant. Its diagonal multiplier can be
neither 1 (the E63 polynomial has no root) nor −1 (the two diagonal
identities above contradict injectivity). Multiplicative power conjugacy
reduces the other scalar-profile possibilities to orders 23 and 46,
represented by `s=2` and `s=5`. Power conjugacy is used to search scalar
profiles; it is not asserted to preserve GL(2,47)-equivariance.

The script `scripts/fo_467_inverse_profile.py` checked each of these two
representatives with a single CP-SAT worker for 45 seconds, first with
inverse profiles and then adding the product constraint. All four runs
returned `UNKNOWN`; none is an UNSAT certificate. Every positive result
would be checked on all 47² input pairs before being recorded.

A separate 60-second `s=1` probe also returned `UNKNOWN`, so no new
idempotent E63/E467 seed at 47 was found. The exact statuses and timings
of these runs are recorded in `data/spectrum/fo_467_inverse_followup.json`.
