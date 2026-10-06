# E667: excluding order-twelve subclasses

As of 2026-10-01, **existence at order twelve remains open**. All the exclusions
in this table are complete Lean proofs, including the two explicitly
registered native LRAT certificate replays. They contain no `sorry`.

| Additional hypothesis at order 12 | Result | Lean declaration in `Spectrum.E667` |
|---|---|---|
| Quasigroup | Necessary for every finite model, not an extra restriction | `E667883.left_injective667`, `E667883.right_injective667` (in `Spectrum`) |
| Commutative | Impossible | `not_commutative_twelve` |
| Idempotent | Impossible | `not_idempotent_twelve` |
| Associative | Impossible; indeed at every nonzero order divisible by 3 | `not_associative_of_three_dvd` |
| Left identity | Impossible at every order divisible by 3 | `not_left_identity_of_three_dvd` |
| Right identity | Impossible | `not_right_identity_twelve` |
| Two-sided identity | Impossible, by either identity exclusion | as above |
| Proper nontrivial quotient | Impossible | `quotient_card_twelve` |

The proofs are in `Spectrum/Equation667Subclasses.lean`,
`Spectrum/Equation667IdempotentTwelve/`, and
`Spectrum/Equation667RightIdentityTwelve/`. The simplicity theorem is in
`Spectrum/Equation667SimpleTwelve.lean`.

## Commutativity: an endomorphism and a parity count

Write `s(x)=x*x`. Finite E667 has cancellation and the rotated identity

```
(x*y) * (s(x*y)*x) = y.
```

Suppose multiplication is commutative. Put `z=x*y`, `t=s(z)*x`. Rotation gives
`z*t=y`, hence `t*z=y`. Rotating `(t,z)` and cancelling gives `s(y)*t=x`.
Rotating `(s(y),t)` then gives `x*(s(x)*s(y))=t=x*s(z)`. Cancel to conclude
`s(x*y)=s(x)*s(y)`. Thus squaring is an endomorphism.

Its image is a quotient of the original magma. At order twelve simplicity
forces that image to have size one or twelve. Size one is impossible: the
previous constant-square argument excludes every order divisible by three.
If the image has size twelve, squaring is bijective. For a fixed square `w=s(a)`,
let `d(y)` be the unique solution of `y*d(y)=w`. Commutativity makes `d` an
involution, and injective squaring makes `a` its unique fixed point. All other
elements pair off, so the carrier has odd size, contradicting twelve.

This proof uses the existing small-quotient and order-six exclusions through
simplicity, but introduces no additional finite search or SAT certificate.

## Left identities and associativity

For an idempotent `e`, the previously proved square-fiber identity is
`s(x)=e ↔ e*(e*x)=x`. A left identity therefore forces every square to equal
`e`, which is impossible at an order divisible by three.

An associative finite quasigroup has a left identity without assuming one:
choose `a`, solve `a*e=a`, and cancel `a` in
`a*(e*x)=(a*e)*x=a*x`. This reduces the associative case to the same argument.

A right identity is a genuinely separate case. For example `x*y=x+5y` over
`F₇` satisfies E667 with right identity zero, but zero is not a left identity.

## Idempotency: a simpler operation and a small refutation

For an idempotent E667 model put `d(x,y)=y*(y*x)`. The equation says
`x*d(x,y)=y`, so `d` is left division. Direct substitution gives

```
d(d(x,d(x,y)),x)=y,     d(x,x)=x.
```

This is the simpler E229 cubic law with idempotency. A permutation fixing zero
puts its zeroth row into the proved chain-label form. The existing cubic
encoding then refutes the twelve-element case in about 0.14 seconds.

The 94,230-clause encoding has 1,728 Boolean variables. Its trimmed LRAT proof
compresses to 180,967 bytes. Lean checks the encoding soundness, the change of
operation, the relabelling, and the certificate. The certificate module builds
in roughly six seconds on this machine; it does not run the search again.

## Right identity: a second checked finite refutation

Here we retain the original E667 multiplication. First move the right identity
to zero, then chain-label its left translation with a permutation fixing zero.
**No conditional diagonal normalization is allowed at this stage:** an
idempotent distinguished element need not make the whole magma idempotent.

The table encoding records `p(x,y,z) ↔ x*y=z` and
`q(x,y,z) ↔ (x*x)*y=z`. It includes Latin constraints, E667, the right-identity
units, and the already proved constant-square, translation-cycle, and
square-fiber consequences. Every group of clauses has its own Lean soundness
proof. CaDiCaL refuted its 137,431 clauses and 3,456 variables in about 1.1 seconds.
The trimmed certificate compresses to 1,207,368 bytes; Lean replay takes about
seven to eight seconds on this machine. A simpler encoding without the extra
consequences exhausted a sixty-second budget, illustrating their practical value.

Both refutations use the repository's `spectrum_native` policy for Lean's
verified LRAT checker. The external solver's report alone is not trusted.
The CNF and proof hashes, timings, and Lean declaration names are in
`data/spectrum/667_{idempotent,right_identity}_twelve.json`.

## What remains, and reproduction

Any order-twelve model must be a simple, noncommutative, nonassociative
quasigroup, with some non-idempotent element and with neither a left nor a
right identity. **Mixed idempotent/non-idempotent models are still possible:**
excluding globally idempotent models does not exclude models containing an
idempotent. These exclusions alone do not eliminate the mixed branch.

A subsequent bounded search refuted the formerly surviving row shape
`(1,1,4,6)` in 89 seconds. The other six shapes exhausted their 180-second CPU
limits. This particular row refutation is **external, not Lean-replayed**.
Together with the preceding external reductions, this leaves six
one-idempotent row shapes and the unchanged 44 idempotent-free shapes, for
**50 remaining shapes**:

```
(1,3,3,5), (1,3,4,4), (1,3,8), (1,4,7), (1,5,6), (1,11).
```

The complete pass, exact CNF hashes and limits are archived in
`data/spectrum/667_order12_subclass_rows.json`. Reproduce it with
`python3 scripts/spectrum_667_subclass_rows.py --seconds 180 --workers 2`.
No searches remain running.

A sixty-second Prover9 attempt to establish closure of the idempotents under
multiplication was inconclusive, but reviewing the saved nine-point models
then **disproved** the proposal. In the first square-endomorphism counterexample
in `data/spectrum/667_883_research.json`, the idempotents are exactly `{0,7,8}`,
while `0*7=2` and `2*2=4`. `Equation667NonclosedIdempotents.lean` now verifies the
model and this failure directly in the Lean kernel. This retained table is a
structural counterexample, not a redundant spectrum seed. It says nothing
against closure of a single squaring fiber, which is a different open claim.

An attempted automorphism identity for the left translation by a right
identity remains unproved. A separate attempt to show that equal squares
remain equal after a right translation also failed: Prover9 exhausted the
search within its weight bound, and Mace4 found no order-eight counterexample
within sixty seconds. These outcomes decide neither direction. None of these
unproved identities has been added as a search constraint.

To verify stored hashes or regenerate the certificates:

```
python3 scripts/spectrum_667_subclasses.py --case idempotent
python3 scripts/spectrum_667_subclasses.py --case right_identity
# Add --solve to either command to rerun CaDiCaL and Lean's LRAT trimmer.
lake build equational_theories.Spectrum.Equation667Subclasses
lake build equational_theories.Spectrum.Equation667IdempotentTwelve.Certificate
lake build equational_theories.Spectrum.Equation667RightIdentityTwelve.Certificate
```

The current `spectrum_667_incremental.py` additionally applies the newly proved
idempotent and right-identity exclusions to order-twelve searches. Its existing
order-fifteen constraints are unchanged. Historical search logs describe the
constraints in use when those particular passes ran.
