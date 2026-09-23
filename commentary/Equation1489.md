This law implies that the squaring map `S: x ↦ x◇x` is surjective.  Explicitly, one has `x = S((C(x) ◇ (x ◇ C(x))) ◇ x)` with `C(x) = (x◇x)◇x` the cubing map.  In a quasigroup, this law implies that the squaring map is bijective.

The finite spectrum is exactly the positive integers other than 2 and 4. In fact,
every allowed order has an idempotent model. A constructive proof using truncated
transversal designs is formalized in `Spectrum.spectrum_1489` and
`Spectrum.idempotent_models_1489` in `Spectrum/Equation1489.lean`; see
[the proof](https://github.com/Timeroot/equational_theories/blob/main/docs/1489_finite_spectrum_theorem.md).

This law cannot hold in a non-trivial semigroup (associative magma).
