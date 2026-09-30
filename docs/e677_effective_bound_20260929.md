# An effective E677 spectrum bound

**Superseded:** the bound is now **164,475**, with a complete Lean proof.
See [the integrated result](e677_integrated_spectrum.md). The certificate below
is retained as a record of the earlier construction.

Every order **n ≥ 42,239,519** admits an E677 magma. This is a
**computer-assisted construction**, with a complete induction argument and
independently checked integer certificates. It is **not yet a complete Lean
proof of that numerical cutoff**. The previously formalized, non-numerical
cofiniteness theorem remains proved in Lean.

The general weighted sieve and the reduction to finite certificates are now
proved in Lean in `Spectrum/PBD/EffectiveSieve.lean` and
`Spectrum/Equation677/EffectiveBounds.lean`. The remaining Lean work is checking
the concrete finite construction and weight data against those interfaces.
There are no new `sorry` declarations.

The cutoff is an existence bound, not an exact spectrum characterization.
Failure of the finite construction to supply a smaller order does not exclude
that order.

## Reproduction

Run:

```sh
python3 scripts/spectrum_effective_bound.py
```

This checks the algebraic seeds, compiles the finite positive-construction
program, recomputes its bitmap, checks all 480 weighted sieve certificates using
exact integers, and verifies the induction hypotheses. Python, a C++ compiler,
and approximately 1 GB of working memory are sufficient. The bitmap is temporary
cache data; it is not committed. The compressed certificate is about 4.7 MB.
No optimizer, model finder, or external design-existence oracle is needed to
check the result.

For an already computed bitmap, `--bitmap PATH` checks the saved digest and all
remaining certificates. That option does not rerun the construction computation.

## Algebraic seeds

For a finite commutative ring, use x*y = ax+by. E677 follows from

    ab + ab³ = 1,        a + a²b² + b³ = 0.

The model is idempotent when a+b=1; in every case 0*0=0. The certificate contains
352,957 scalar recipes over Z/p, with p at most ten million. Each recipe is
checked directly by modular arithmetic. Primality is unnecessary for this
operation: it works over Z/n whenever the two displayed identities hold.

There are also 3,750 quotient-ring recipes. Their data specify p, a monic
polynomial g, and the polynomial coefficient a; b is the class of X. Their
order is p^deg(g). The checker performs the two identities by polynomial
arithmetic modulo p and g, and checks idempotence where claimed. Irreducibility
of g is unnecessary for the model: a monic quotient has the required finite
cardinality even when it is not a field.

The useful polynomials arise by eliminating a:

    (b⁴−b³+b²−b+1)(b⁴+b³+2b²+2b+1) = 0.

The search used finite-field factorization to obtain roots efficiently. The
checker uses only the resulting coefficients and their ring identities.

Additional seeds are every positive fourth-power order, supplied by the existing
idempotent companion-matrix construction, and the existing pointed model at
order 9. The latter's 81 equation instances and its fixed point are checked
explicitly.

## Positive construction rules

All models used in this computation have a distinguished idempotent point.
Cartesian products preserve that property.

A field of order q supplies TD(q+1,q), and transversal designs multiply. Thus
TD(k,q) exists if every maximal prime-power factor of q is at least k−1.
The finite computation uses only this sufficient criterion. These are positive
design constructions, not assumptions that other orders lack designs.

Finite idempotent E677 models have the discreteness property proved in
`Equation677/Gluing.lean`: when the original two inputs differ, each intermediate
multiplication uses distinct arguments. Consequently they can fill transversal
blocks while the group fillings are arbitrary E677 models.

The closure uses:

* Cartesian products.
* A common point: an idempotent block model at k, a pointed group model at q+1,
  and TD(k,q) give a pointed model at kq+1.
* One truncated group: idempotent block models at k and k+1, TD(k+1,q), and
  pointed group models at q and r≤q give a model at kq+r.
* The same truncated construction with a common point: group models at q+1
  and r+1 give order kq+r+1.

If all group fillings are idempotent, the resulting model is idempotent. When
using a common point, identify the fixed points of all groups. Distinct inputs
in a single group evaluate wholly inside that group. Inputs from different
groups evaluate wholly inside their unique transversal block, by discreteness.
This proves the law and explains why nonidempotent group fillings are permitted.

The program stores orders and construction closure in bitmaps. A translated
prefix of a bitmap represents all permitted truncated-hole fillings at once;
no large multiplication tables are constructed or checked.

## The finite facts

Put C=42,239,519 and R=6,000,000. The checked closure supplies:

1. Every order from C through 500,000,000, in particular through
   81R=486,000,000.
2. Every odd order q with R≤q<C.
3. All 217,332 hole orders appearing in the weighted certificates, each positive
   and at most R.
4. Idempotent block models at 80=5·16 and 81=3⁴.

The bitmap has SHA-256
`8aaf258cd49c4aba4e7770d128792a6644a1129a777cf51be9b240e5b15fd2f2`
when truncated to its declared domain 0 through 500,000,000.
The independent checker verifies every algebraic seed, every required interval,
and every selected hole's membership in this bitmap. Reproduction verifies the
bitmap by recomputing the positive construction closure.

## The weighted sieve

For each t in {0,…,479}, the certificate supplies a finite collection of indices
j with hole orders r_j=480j+t, positive integer weights w_j, and integer bounds
c_p for the primes

    5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79.

For each p and every residue u modulo p, it verifies

    Σ_{j ≡ u (mod p)} w_j ≤ c_p,        Σ_p c_p < Σ_j w_j.

These are exact integer checks. Linear programming was used only to discover
weights; rounding was followed by independent integer verification. Floating
point calculations are not evidence for the inequalities.

Given n>81R, take t≡n−80 (mod 480), with 0≤t<480, and set

    a=(n−t)/80,        q_j=a−6j.

Then a≡1 (mod 6), 80q_j+r_j=n, and every q_j is positive, odd, and at least R.
For a fixed prime p in the displayed list, the indices making p divide q_j lie
in a single residue class modulo p, because 6 is invertible modulo p. If every
candidate q_j had a forbidden prime divisor, its positive weight would be
counted at least once among these residue classes. The two inequalities rule
this out. Hence some q_j has no prime divisor at most 80: 2 and 3 are already
excluded by q_j≡1 (mod 6). The cyclic-ring construction supplies TD(81,q_j).
Also r_j≤R≤q_j, as required for truncation.

This argument is `EffectiveSieve.affine_avoid` and
`E677.EffectiveBounds.HoleCertificate.decompose` in Lean.

## Closing the induction

Use strong induction on n≥C. The finite check handles n≤81R. Otherwise choose
q,r by the weighted sieve. The hole has a certified model and q<n is odd.
If q<C, use finite fact 2; if q≥C, use the induction hypothesis. The idempotent
block models of sizes 80 and 81 and TD(81,q) now give a model of order
80q+r=n.

This final argument is `Spectrum.E677.EffectiveBounds.tail`. Its hypotheses are
finite model and weight certificates; the theorem itself has no numerical
existence assumption or design-existence conjecture.

## Effective bounds for E1083 and E1286

The subsequent work in
[`1083_1286_effective_tails_20260930.md`](1083_1286_effective_tails_20260930.md)
extends the finite searches to actual infinite tails: 246,119,111 for E1083 and
4,222,119,949 for E1286. It uses compressed interval certificates and a uniform
22,000-integer gap for TD(1009,q). As here, the concrete numerical certificates
await Lean checking.
