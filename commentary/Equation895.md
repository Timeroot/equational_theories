## The Boolean group law

The laws 895, 1334, 1571, and their duals are equivalent characterizations of the operation in [Boolean groups](https://teorth.github.io/equational_theories/blueprint/implications-chapter.html#1571_impl), namely groups of exponent 2, which are automatically abelian.  This was shown for law 1571 [by Mendelsohn and Padmanabhan](https://teorth.github.io/equational_theories/blueprint/sect0001.html#mendelsohn-padmanabhan).

In particular, it implies the [commutative law 43](https://teorth.github.io/equational_theories/implications/?43) and [associative law 4512](https://teorth.github.io/equational_theories/implications/?4512).

Since division coincides with multiplication for groups of exponent 2, the law also implies Tarski's axiom [543](https://teorth.github.io/equational_theories/implications/?543).

For other laws (of minimal order `2*n`) characterizing groups of exponent `n` for `n=4` and `n` odd, see the commentary of [law 163669](https://teorth.github.io/equational_theories/implications/?163669).

The free magma on some set `Σ` of generators for this law is the set `𝒫(Σ)` of finite subsets of `Σ`, with the magma operation being the symmetric difference.

Its positive finite spectrum is exactly the powers of two. This is proved in
Lean as `Spectrum.Catalogue.exact_895`, including the Boolean-group
reconstruction and cardinality argument; see
[the proof description](../docs/powers_two_and_bookend_spectra.md).
