# E1279 transfers to E704 and E1110: inverse-profile follow-up

28 September 2026. Both finite FO directions remain open. This pass proves
additional restrictions on homogeneous targets in Lean and records stronger,
bounded searches. No new spectrum exclusion or general definability negative
is asserted.

The scalar source operations `14x+36y` over F71 and `42x+38y` over F47
satisfy E1279. A parameter-free definable operation on either source must
commute with every nonzero scalar multiplication. On the square of the
source it must also commute with GL(2,p). The earlier note
[`fo_1279_transfers_research.md`](fo_1279_transfers_research.md) gives the
independent-vector coefficient constraints. The remaining scalar subproblems
are E704 over F71 and E1110 over F47. A positive scalar solution would itself
be a useful finite model, but would not establish a universal FO transfer.

## Permutation equations

Write a homogeneous operation as

```
p(0,y) = c*y,
p(x,y) = x*f(y/x) for x != 0,
f(1) = s.
```

Every finite E704 or E1110 operation is a quasigroup. For E704, the identity
is `L_y² R_y D = id`, where `D(x)=p(x,x)`; for E1110 it is
`L_y R_y L_y D = id`. Finiteness makes the factors bijective. Thus `f` has
an inverse `g`, and both right-column profiles below are permutations:

```
H(0)=c, H(t)=f(t)/t for t != 0;
R(0)=c, R(t)=t*f(1/t) for t != 0.
```

In either law the instance `(x,y)=(1,0)` gives

```
c²*s*f(0) = 1.
```

For E704, normalizing `y=1` gives the complete equations

```
f²(H(t)) = 1/(s*t) for t != 0,
f²(c) = 0.
```

Using the inverse row turns these into the single lookup
`f(H(t))=g(1/(s*t))`, with the right side interpreted as `g(0)` at zero.
For E1110 the corresponding equations are

```
f(R(f(t))) = t/s,
R(f(t)) = g(t/s).
```

The product theorem proved in
[`fo_704_467_inverse_followup.md`](fo_704_467_inverse_followup.md) gives
`f(0)=-c*g(0)`. Combining it with the common zero constraint yields

```
f(0) = 1/(c²*s),
g(0) = -1/(c³*s).
```

Additional consequences used to strengthen propagation are
`f(f(0))=-c³` for E704 and `f(c²*s)=-1/c` for E1110. They follow by
substituting the zero of `f` into the normalized identity. These equations
are necessary for all homogeneous models; no affine assumption is made.

## Lean results

[`Homogeneous7041110.lean`](../equational_theories/Definability/Homogeneous7041110.lean)
proves left and right cancellation for both finite laws, the common zero
constraint, and the exclusion of the diagonal multiplier `s=-1` in
characteristic different from two. Its public restrictions are

* `Definability.Homogeneous7041110.zero_constraint_704`;
* `Definability.Homogeneous7041110.zero_constraint_1110`;
* `Definability.Homogeneous7041110.square_ne_neg_one_704`;
* `Definability.Homogeneous7041110.square_ne_neg_one_1110`.

For the last two, assume `p(1,1)=-1`; homogeneity gives `p(-1,-1)=1`.
E704 at `(-1,1)` and left cancellation give `p(1,-1)=1`.
Homogeneity then gives `p(-1,1)=-1=p(1,1)`, contradicting right cancellation.
For E1110 the same law instance gives `p(-1,1)=1`, then homogeneity gives
`p(1,-1)=-1=p(1,1)`, contradicting left cancellation.
These are algebraic Lean proofs using only the standard three axioms.
The full inverse-profile search reduction is documented above; it is not
claimed to have a complete Lean implementation in this module.

## Reproducible bounded searches

`scripts/fo_homogeneous_quasigroups.py` implements the inverse-row encoding
and independently checks every positive output against every instance of
the original law on the full multiplication table.

As positive regression checks, the strengthened encoding recovered the
known E704 affine model `21x+27y` and E1110 affine model `6x+28y` over F29.
The stronger constraints reduced these small checks to about one second.

The E1110 probes at F47 tested multipliers representing orders 1, 2, 23,
and 46 for 60 seconds each, then repeated the two nontrivial remaining
orders with the product constraint for 60 seconds each. The E704 probes
at F71 tested all eight multiplicative orders for 60 seconds each, then
repeated them with the product constraint for 45 seconds each.
The `s=-1` cases were infeasible, as the Lean lemmas now prove; all other
searches returned `UNKNOWN`.

Representatives of multiplicative orders suffice for scalar-profile searches
because conjugating by a power permutation of the field changes the square
multiplier within its order class. This conjugacy is not asserted to preserve
GL(2,p)-equivariance. The separate idempotent obstruction for vector sources
was already recorded in the earlier note.

Exact statuses, parameters, and positive regression witnesses are saved in
[`fo_704_1110_inverse_followup.json`](../data/spectrum/fo_704_1110_inverse_followup.json).

```sh
python3 scripts/fo_homogeneous_quasigroups.py 704 71 --seconds 45
python3 scripts/fo_homogeneous_quasigroups.py 1110 47 --seconds 60 --multiplier 2 --multiplier 5
lake build equational_theories.Definability.Homogeneous7041110
```
