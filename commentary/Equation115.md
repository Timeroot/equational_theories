This law implies that left and right multiplications are surjective, the squaring map `S: x ↦ x◇x` is injective, and `B: x ↦ x◇(x◇x)` is surjective, with `B(S(x)) = x`.  The operations defined by `x : y = (y ◇ y) ◇ x` and `x / y = (y ◇ y) ◇ (x ◇ x)` satisfy `y ◇ (y : x) = x` and `(x / y) ◇ y = x`, hence they can serve as (not necessarily unique) left and right divisions.  In addition, `(y / x) : y = x`.

For finite magmas, or for quasigroups, the dual [law 219](https://teorth.github.io/equational_theories/implications/?219) is equivalent to [law 880](https://teorth.github.io/equational_theories/implications/?880) `x = y ◇ ((x◇y) ◇ (x◇y))`, which is a twist of the semi-symmetric quasigroup [law 14](https://teorth.github.io/equational_theories/implications/?14) `x = y ◇ (x◇y)`.

This law cannot hold in a (non-trivial) semigroup (associative magma).

The finite spectrum is exactly the positive integers except {2, 6}. This is proved in Lean by `Spectrum.Catalogue.exact_115`; see the [construction and exclusion proofs](../docs/quasigroup_spectra.md).
