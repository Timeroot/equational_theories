# Homogeneous E1516 models and finite FO transfers

28 September 2026. A complete **Lean proof** now refutes
finite parameter-free FO transfers **E467 → E1516**, **E704 → E1516**, and
**E1279 → E1516**, and therefore their unrestricted variants. The same
argument also reproves E1110 → E1516, already negative on the board.
There are no remaining classification hypotheses or `sorry` declarations in
these results. Four compressed LRAT certificates are replayed by Lean's
checker using the repository's explicit native-computation trust boundary.

The public results are `Equation1516_not_definableFromFin_Equation467`,
`Equation1516_not_definableFromFin_Equation704`, and
`Equation1516_not_definableFromFin_Equation1279` in
[`Definability/Homogeneous1516.lean`](../equational_theories/Definability/Homogeneous1516.lean).
The corresponding names without `Fin` prove the unrestricted negatives.

Here `B → A` means that every finite B-magma admits a parameter-free
FO-definable A-operation on its carrier. The argument concerns definability,
not a spectral separation: both source and target spectra contain 841.

## The mathematical reduction

Take V=F29² and the following scalar source operations:

| Source | Operation on V |
|---|---|
| E467 | `8x+12y` |
| E704 | `21x+27y` |
| E1110 | `6x+28y` |
| E1279 | `4x+11y` |

The operations satisfy their respective laws coordinatewise. Every invertible
linear transformation of V is a source automorphism. Hence any parameter-free
FO-definable companion operation q is GL(2,29)-equivariant.

Reflection in an axis shows that q preserves that axis. Its restriction p to
the first axis is a homogeneous operation on F29:

    p(tx,ty)=t p(x,y) for every t≠0.

If q satisfies E1516, then p does too. The completed Lean classification
below says that every such p has `p(1,1)=1`. Transport by GL(2,29) then makes q
idempotent at every vector. Consequently q satisfies E63 as well.

The already proved GL obstruction for E63 forces a root in F29 of

    t⁵+t⁴+1 = (t²+t+1)(t³−t+1).

There is no such root. Thus the definable companion cannot exist.

The reduction, including preservation of axes and the step from one
idempotent vector to all vectors, is proved in
[`Definability/GLTwo1516.lean`](../equational_theories/Definability/GLTwo1516.lean).
Its generic theorem `Definability.GLTwo1516.not_definableFromFin` takes the
homogeneous classification as a hypothesis. The concrete public negatives
discharge it with `Definability.Homogeneous1516.classification`; they have
no such assumption. The generic reduction uses only `propext`,
`Classical.choice`, and `Quot.sound`.

## The completed Lean classification

`Homogeneous1516/Normalization.lean` proves the normalized equations below,
including both right-cancellation constraints, over any finite field of
characteristic other than two. `PowerReduction.lean` transports operations
by multiplicative power permutations of F29 and checks that every nonzero
multiplier other than one reduces to one of **2, 4, 7, 12, 28**.

The multiplier **28 = −1** is impossible by the algebraic theorem
`square_ne_neg_one`. For **2, 4, 7, 12**, `Encoding.lean` proves that every
normalized operation satisfies a one-hot CNF. `Bridge.lean` connects this to
the original homogeneous operation. The four modules in `Cases/` check the
saved LRAT refutations and apply `check_sound`.

`Classification.lean` combines these results into `classification`, asserting
`p 1 1 = 1`, and `idempotent`, asserting `∀ x, p x x = x`. The concrete
source law checks are in `Sources.lean`. Thus the finite classification
and every step from it to the FO negatives are now formalized.

The checked CNFs were independently exported from Lean and matched the
Python-generated solver inputs byte for byte. The four compressed proofs
total approximately 33.4 MB. The final declarations carry completeness
checks rejecting pending proofs and undeclared axioms.

## The finite classification and its exact scope

Every homogeneous operation on Fp is determined by c and a function f:

    p(0,y)=cy,
    p(x,y)=x f(y/x) for x≠0.

The origin satisfies `p(0,0)=0`. In a finite E1516 magma, left and right
translations and squaring are bijective. Thus f is a permutation, and
`c`, `f(0)`, and `s=f(1)` are all nonzero. The normalized law is exactly

    f(f(0))=c⁻¹,
    f(c²/s)=0,
    f(f(f(t))/(st))=1/(st) for every t≠0.

If g=f⁻¹, the last equation becomes

    f(f(t)) = st g(1/(st)).

This form has one variable-index lookup instead of two and propagates much
better in the constraint solver. Right cancellation additionally says that
`c` and the values `f(t)/t` for `t≠0` form a permutation of Fp.

The saved CP-SAT run at p=29 proves infeasibility for **each s=2,…,28**.
Each case took at most about seven seconds with four workers. The case s=1
has a directly verified positive solution, found in about 34 seconds. Its
profile is saved too; idempotent E63 existence at 29 was already known, so
this positive result does not improve the spectrum.

These results exhaust the homogeneous class. They do not exclude arbitrary
E1516 operations of order 29, and they do not assume that homogeneous
operations are affine. Indeed the positive s=1 model is nonlinear.

For an alternative case reduction, transport the carrier by `x↦x^k`, where
k is coprime to 28. Homogeneity is preserved and the square multiplier becomes
`s^k`. Thus it suffices to check the multiplier orders 2,4,7,14,28, represented
by 28, 12, 7, 4, 2 respectively. The recorded run checks every multiplier directly.

## Historical searches and reproduction

[`scripts/fo_1516_homogeneous29.py`](../scripts/fo_1516_homogeneous29.py)
contains the reduced encoding and an independent complete-table verifier.
[`data/spectrum/fo_1516_homogeneous29.json`](../data/spectrum/fo_1516_homogeneous29.json)
contains all 28 outcomes, the positive profile, and the four source coefficient
pairs. The default checker rechecks all source laws, all positive-model law
instances and scalar symmetries, and parameter coverage. It does not reinterpret
saved solver statuses as a Lean proof. The separate LRAT certificates now
supply the completed Lean proof.

```
python3 scripts/fo_1516_homogeneous29.py
python3 scripts/fo_1516_homogeneous29.py --search 29 180 --output /tmp/h29.json
python3 scripts/fo_1516_certificates.py
LEAN_NUM_THREADS=4 lake build equational_theories.Definability.Homogeneous1516
```

`scripts/fo_1516_certificates.py --solve` regenerates all four proofs with
CaDiCaL. Its default mode checks the proof hashes and generated Lean sources;
Lean performs the logically authoritative refutation checks. Certificates
and their manifest are in `data/definability/1516_homogeneous_lrat/`.
The earlier experimental bit-vector certificate is no longer needed.

The same search method produced new idempotent models of orders 31 and 41,
which *have* been formalized and transferred to further spectrum cells; see
[the new seed constructions](63_homogeneous31.md). A homogeneous idempotent
search at 13 was infeasible; the corresponding order 47 search timed out at
120 seconds. Neither observation is an unrestricted spectrum exclusion.
