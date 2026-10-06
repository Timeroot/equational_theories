# E667: translation cycles and constant squaring

The equation under study is

```
x = y * (x * ((x*x) * y)).
```

Every finite model is a quasigroup. Write `D(x)=x*x` and `L_x(y)=x*y`.
The results below are proved in
`equational_theories/Spectrum/Equation667ConstantDiagonal.lean`. The
algebraic results and divisibility-by-three obstruction use no SAT
certificates, `native_decide`, or admitted steps. The stronger full spectrum
restriction additionally transfers the existing checked exclusion of
six-point Mendelsohn systems. These results restrict proposed
models at orders 12 and 15; they do **not** exclude arbitrary models at
either order.

## A forbidden translation cycle

No left translation can have its row index in a genuine three-cycle.
If `L_x³(x)=x`, the equation at `(x,x)` says
`L_x²(L_D(x)(x))=x`. Cancel `L_x²` to obtain `D(x)*x=x*x`, and cancel the
right translation by `x` to obtain `D(x)=x`.

There is also a useful two-cycle consequence: if `L_x²(x)=x`, then `D(x)`
is idempotent. The same first cancellation gives `D(x)*x=x`. Applying the
equation to `(D(x),x)`, then cancelling `L_x`, gives
`D(x)*(D(D(x))*x)=x`. Cancel `L_D(x)` and then the right translation by `x`
to conclude `D(D(x))=D(x)`.

These are `three_cycle_implies_idempotent` and
`two_cycle_square_idempotent`. In particular, computational branches that
put the distinguished element in a three-cycle can be discarded
algebraically at every order.

## Constant squaring gives a semisymmetric loop

Suppose `D(x)=e` for every `x`. Put `J(x)=e*x`. The equation becomes

```
y * (x * J(y)) = x.
```

Set `x=e` and cancel `L_y` against `y*y=e` to get `J²(y)=y`. Set `y=e`
to get `x*e=J(x)`. Thus `J` is an involution and is both the left and
right translation by `e`.

An entry `x*y=z` can be rotated to `z*J(x)=y`: substitute `z,x` in the
equation and cancel `L_x`. Two rotations give `y*J(z)=J(x)`; three give
`J(x)*J(y)=J(z)`. Consequently `J` is an automorphism.

Define `x∘y=J(x*y)`. This has identity `e` and constant square `e`.
The twice-rotated identity gives

```
y ∘ (x ∘ y) = J(y * J(x*y)) = J(J(x)) = x.
```

Hence `∘` is a semisymmetric loop. Deleting its identity yields an
idempotent semisymmetric quasigroup (a Mendelsohn system) of order `n-1`.
Its distinct ordered pairs fall into three-cycles, so
`(n-1)(n-2)` is divisible by three. Therefore **`n` cannot be divisible
by three**. The full established spectrum theorem for semisymmetric loops
also excludes `n=7`.

Conversely, twisting a semisymmetric loop's output by an involutive
automorphism gives a constant-diagonal E667 operation. The forward
construction and cardinality restriction are formalized. The general fact
that involutive automorphism output twists preserve E667 is now formalized
in `Equation667AutomorphismTwist.lean`; see the
[nonlinear construction note](e667_nonlinear_constructions_20261004.md).

The public Lean declarations are `ConstantDiagonal.toLoop`,
`ConstantDiagonal.map_op`, `ConstantDiagonal.orders`, and
`ConstantDiagonal.not_constant_of_three_dvd`. Thus any model at **12 or
15 must have a nonconstant diagonal**. Earlier unsuccessful searches in
the constant-diagonal family can now be replaced by this short proof.

## A square-fiber constraint

For an idempotent `e`, even when the whole diagonal is not constant,

```
D(x)=e  if and only if  L_e²(x)=x.
```

Indeed the equation at `(e,x)` says `x*L_e²(x)=e`; left cancellation
gives the equivalence. Therefore the fiber above `e` is exactly the union
of the one- and two-cycles of `L_e`, and is preserved by `L_e`.
These statements are `square_fiber_iff` and `square_fiber_invariant`.

Whether such a fiber is always closed under the original multiplication
is **unproved**. A bounded Prover9 attempt did not establish it. Mace4
found no counterexample at order 8 after exhausting that domain, while
the order-9 and order-10 attempts timed out. These exploratory outcomes do not justify
adding fiber closure as a search constraint.

Additional 20-second Prover9 probes for analogous universal obstructions
at translation-cycle lengths 5, 7, 8, and 12 were inconclusive. Those cycle
lengths have not been discarded.

## Independent audit of the small-quotient obstruction

The simplicity argument in `e667_construction_research.md` checks out.
A quotient of a finite E667 magma is itself finite and satisfies E667, so
it is Latin. For any two quotient elements, a left translation in the
original magma injects one fiber into the other; reversing the roles of
the fibers proves equal cardinality. Thus quotient orders divide the
original order. An idempotent quotient element has a fiber closed under
multiplication, and that fiber is itself an E667 model.

These abstract statements are formalized in `Equation667Quotients.lean`:
`fiber_card_eq`, `card_eq_mul_fiber`, `idempotent_fiber_model`, and
`model_of_idempotent_quotient`. In particular, the argument does not assume
that a magma homomorphism preserves unspecified division operations.

The exceptional five-point quotient's three-point-fiber obstruction is
formalized separately in `Equation667FiberThree.lean`. Every Latin block
on three points is affine: each row and column is an affine permutation;
the possible mixed coefficient must vanish because all three row slopes
are nonzero. This avoids enumerating large operations. Comparing the two
coefficients of E667 gives the sign identities in the construction report.
Multiplying fifteen selected identities makes every sign occur twice on
the left and leaves an odd number of minus signs on the right, a
contradiction. The final `no_quotient_five` theorem applies to a surjective
homomorphism from an arbitrary fifteen-element carrier to
`q(i,j)=3i+3j+1 mod 5`.

The order-2 and order-4 classifications are no longer needed for their
idempotent consequence. `Equation667SmallQuotients.lean` proves that
consequence directly. At order two every permutation has cycles of length
one or two. At order four, choose a row with a fixed point, which exists
because every column is a permutation. All cycles in that row have length
at most three; the period-two and period-three lemmas above then produce
an idempotent. Only a tiny unary-permutation check is used, with no
multiplication-table enumeration. `exists_idempotent_of_card` transfers
this result to arbitrary finite carriers.

The former external computational input to **simplicity at order 15** was
the order-5 classification. Its idempotent-free part is now fully proved in
`Equation667FiveClassification/`, and `quotient_card_fifteen` is complete.
See `e667_mace4_and_order15.md`. The independent Python enumerator visits all
output relabelings of every Latin square with
normalized first row and reevaluates E667 after relabeling. That
normalization does not silently assume that arbitrary relabelings preserve
the law. The full saved enumeration counts remain research evidence; the
idempotent-free isomorphism classification used in simplicity is now Lean-proved. Simplicity at order 12 is completely formalized in
`Equation667SimpleTwelve.lean`: `Spectrum.E667.quotient_card_twelve` states
that every surjective homomorphism from a twelve-element E667 magma to
another finite E667 magma has a target of order one or twelve. It reuses
the existing registered checks excluding orders three and six;
`spectrum_assert complete` verifies its dependencies.

A separate normalization caveat matters for larger SAT searches:
`spectrum_small_pair_search.encode(..., normalize=True)` includes
`f(0,0)=0 → ∀x, f(x,x)=x`. A refutation with the first-row index fixed
therefore rules out the fully idempotent branch. It does not establish
that all models are idempotent-free. To study a single distinguished
idempotent, remove that conditional diagonal constraint.

## The six-failure twelve-point near-model

The saved trade-search near-model in
`.cache/e667-constructions/near12-six.json` is Latin and satisfies 138 of
the 144 E667 instances. It does not supply evidence against the square-fiber
lemma: its row at the idempotent `1` fixes ten points and exchanges `3,5`,
so `L_1²` is the identity on **all twelve points**. The already proved
`square_fiber_iff` would therefore force every square to be `1`. Its actual
squares at `3,5` differ; the failures at equation instances `(1,3)` and
`(1,5)` are exactly this discrepancy.

More generally, a proper square fiber above an idempotent must omit at
least three points. Its complement is invariant under `L_e`; on an
invariant set of one or two points every permutation squares to the
identity, contradicting membership in that complement. This elementary
consequence is weaker than the proposed half-size bound and does not
require closure of the fiber. It is formalized as
`Spectrum.E667.square_fiber_complement_card_ge_three`: for any outside
point `x`, the points `x,L_e(x),L_e²(x)` are three distinct outside points.
The module builds in 6.7 seconds and `spectrum_assert complete` passes.

Both saved nine-point E667 models have bijective squaring, so their
idempotent square fibers are singletons. They do not refute square-fiber
closure. However, in the saved non-endomorphism nine-point model,
`L_e²` fails to preserve multiplication for each of its three idempotents.
One therefore cannot prove closure by simply asserting that the square
fiber is the fixed-point set of an automorphism.

One further 90-second Prover9 attempt, supplied with the proved fiber
invariance and additional immediate conditional identities, did not prove
closure. No half-size bound or closure property is assumed in any Lean
proof or licensed search restriction.
