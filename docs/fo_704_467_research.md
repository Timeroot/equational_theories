# E704 to E467: finite first-order transfer attempt

28 September 2026. Here `B -> A` means that every finite B-model has a
parameter-free first-order definable A-operation on the same carrier.

**E704 -> E467 remains open after this attempt.** A related direction,
**E704 -> E63, is now disproved in Lean.** None of the searches below excludes
an unrestricted E467 model at order 31 or 47.

## A finite FO obstruction to E704 -> E63

On `F_29^2`, take the coordinatewise operation

    x * y = 21x + 27y.

It satisfies E704: expansion of `y*(y*((x*x)*y))` gives
`734832x + 20271y = x` modulo 29. Every invertible linear map is an
automorphism. Consequently every first-order definable companion operation
must commute with the general linear group.

The shared theorem in `Definability/GLTwoE63.lean` shows that a
GL(2,K)-equivariant E63 operation, for a finite field of odd characteristic,
would give a root of `t^5+t^4+1` in K. Briefly, write its value on an ordered
basis as `a*x+b*y`. Following E63 on that basis first forces `b != 0` and
`a(1+b) != 0`, then gives

    ab(1+b) = 1,       a+b^3 = 0.

Eliminating a gives `b^5+b^4+1=0`. There is no such root in F_29.

The source calculation, no-root check, and finite FO negative are formalized
in `equational_theories/Definability/GLTwo704.lean`:

* `Definability.GLTwo704.source_models`;
* `Definability.GLTwo704.no_root`;
* `Equation63_not_definableFromFin_Equation704`.

The final theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
It also rules out the unrestricted FO transfer, since a universal definition
would work on this particular finite source. The counterexample has 841
points and is given by a formula; no 841-by-841 operation table is needed.
This is a definability obstruction, not a spectrum exclusion at order 841.

## Reducing the original E467 target by scalar symmetry

The source E704 operations `3x+12y` on F_31 and `4x+20y` on F_47 commute with
every nonzero scalar multiplication. Therefore an FO-definable target q must
have the form

    q(0,y) = d*y,
    q(x,y) = x*h(y/x)       when x != 0,

where `q(0,0)=0`, d is a scalar, and h is a function on F_p. This describes
every scalar-equivariant binary operation, not just affine operations.

Every finite E467 operation is a quasigroup, and its square map S is a
permutation. Its left translations are surjective directly from E467 and
therefore bijective. The existing proof of
`Eq467.Finite.Equation467_implies_Equation2847` also establishes
`S^(-1)(x)=x*q(x,x)`. Finally,

    L_y^(-1)(x) = L_x^2(S(y))

is bijective as a function of y; this gives the right cancellation needed for
the quasigroup claim.

Put `c=h(1)`. Thus h is a permutation, `c,d,h(0)` are nonzero, and the
following constraints are necessary:

    h(c) = 1/c,                  h(c^2) = c^2,
    h(d^2*c) = 0,                d*h(h(0)) = 1,
    h(t*h(h(c/t))) = t           for every nonzero t.

The last three displayed constraints, together with the definition of q,
are the full E467 identity after normalizing a nonzero y to 1 and handling
y=0 separately. The first two are useful redundant consequences. The first
comes from the formula for S inverse. For the second use E2847,
`x=(S^(-1)(x)*x)*x`, and substitute the first constraint.

Right cancellation gives another useful constraint: the p values

    d, and t*h(1/t) for t != 0

are pairwise distinct. This reduces the prospective 31-by-31 target table to
32 scalar parameters, without assuming that the target is affine.

## What the bounded searches actually showed

The reproducible script is `scripts/fo_704_467_research.py`; its default
output is saved in `data/spectrum/fo_704_467_research.json`.

* The complete shifted-power family `h(t)=a+b*(t+s)^k`, with b nonzero and
  `gcd(k,p-1)=1`, has no solution at p=31 or p=47. This checks 230,640 and
  2,235,508 coefficient tuples respectively. The test allows the independent
  coefficient d of the zero row: E467 forces it to be `1/h(h(0))`.
  The family includes every affine h and every shifted, scaled power
  permutation. Its exhaustion is not an exhaustion of all h.
* Unrestricted scalar-equivariant Z3 probes at p=31 timed out: two integer
  encodings at 120 seconds each, and a bit-vector encoding at 90 seconds.
  The bit-vector version can be rerun with `--smt 31 --timeout 90`.
* A separate CP-SAT probe fixed c in turn. The values -1 and the nontrivial
  cube roots of 1 are impossible already from the two redundant h
  constraints. All other 27 values timed out: 3 seconds per value except
  c=1, which received 30 seconds. No CP-SAT exclusion is asserted.

## A stronger restriction for vector-power sources

Replacing the source by its square on `F_p^2` requires GL(2,p)-equivariance.
Write `q(x,y)=a*x+b*y` on independent pairs and `q(y,y)=c*y`. Applying E467
to a basis forces

    ab(1+b)=1,                 a+b^3*c=0.

Indeed c is nonzero by injectivity of S; if b were zero, or `a(1+b)` were
zero, the last E467 output would lie on the wrong coordinate axis. The
remaining evaluation gives the two coefficient equations. In particular

    c = -1/(b^4*(1+b)),        b != 0,-1.

The restriction of q to a line must still solve the scalar problem above,
with this same c. Unlike E63, these equations leave c free, so the shared
root obstruction does not immediately settle E467. A next useful step is a
complete combinatorial treatment of the reduced permutation equations, or
their solution for one of the allowed values of c. A positive scalar
solution alone would already give a new E467 model at 31 or 47; it would
not prove the universal FO transfer from E704.
