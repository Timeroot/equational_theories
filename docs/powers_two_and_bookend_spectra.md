# Powers of two and the bookend spectrum

All thirteen exact-spectrum entries covered here have complete Lean proofs,
using only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, native
computation, or trusted external prover result is used.

## E895 and E898: exactly the powers of two

The two families are:

- E895, E1334, E1571, E2113, E2308, E2789.
- E898, E1368, E1587, E2116, E2316, E2805.

Every law in these families has positive finite spectrum
`{2^k | k : ℕ}`. Existing implication and duality proofs transfer the two
representative results to all twelve laws.

For E895, the existing reduction to E1571 supplies associativity, commutativity,
the identity `x = y ◇ (y ◇ x)`, and equality of all squares. Choosing any anchor
`a`, the magma operation is the multiplication of a commutative group with
identity `a ◇ a` and inverse `x⁻¹ = x`. Thus it is a 2-group, and Mathlib's
`IsPGroup.exists_card_eq` gives power-of-two cardinality.

For E898, define

```
x + y = ((a ◇ x) ◇ (y ◇ a)) ◇ a.
```

The omitted reduction in §3.3 of the note has now been reconstructed: this
operation satisfies E895. A 22-clause first-order derivation is replayed as
ordinary Lean proof steps in `Spectrum/BooleanReduction.lean`. The original
operation need not itself satisfy E895. Both this reduction and the group
reconstruction work on arbitrary nonempty carriers, finite or infinite.

The opposite inclusion was already proved by `power_two_895` and
`power_two_898`, constructing models at every power of two.

Main declarations:

- `Spectrum.BooleanReduction.law` in `Spectrum/BooleanReduction.lean`.
- `Spectrum.BooleanGroup.group`, `Spectrum.BooleanGroup.cardinality`,
  `Spectrum.orders_895`, and `Spectrum.orders_898` in
  `Spectrum/BooleanCardinality.lean`.
- `Spectrum.Catalogue.exact_895`, `exact_898`, and the ten transferred exact
  theorems in `Spectrum/Catalogue.lean`.

## E167: exactly the positive orders congruent to 0 or 1 modulo 4

Let `T(x,y) = (x ◇ y, y ◇ x)`. The bookend identity
`x = (y ◇ x) ◇ (x ◇ y)` says `T²(x,y) = (y,x)`.
Consequently the coordinate swap has even permutation sign.

For a finite linearly ordered carrier, decompose ordered pairs into diagonal
pairs and the two orientations of each strictly increasing pair. If there are
`u` increasing pairs on an `n`-element carrier, this gives

```
n*n = n + 2*u.
```

Coordinate swap has sign `(-1)^u`. Its even sign forces `u` even, so
`n ≡ 0` or `1 (mod 4)`.

Conversely, either residue makes `u` even. Enumerate the increasing pairs as
`Fin k × Bool`, grouping them into pairs. With an additional orientation bit,
the map

```
((i,c),b) ↦ ((i,!c), xor b c)
```

squares to orientation reversal. Fix the diagonal and transport this map back
to the ordered pairs, obtaining `T² = swap`. Such a map automatically commutes
with coordinate swap, so defining `x ◇ y` as the first coordinate of `T(x,y)`
gives an E167 magma.

The construction and obstruction are in `Spectrum/Equation167.lean`:
`Bookend.pairEquiv`, `Bookend.swap_sign`, `Bookend.root_twice`, and
`Bookend.law_of_root`. The final statements are `Spectrum.models_167`,
`Spectrum.orders_167`, and `Spectrum.exact_167`; the catalogue exposes
`Spectrum.Catalogue.exact_167`.

## Validation

```
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
lake env lean scripts/test_spectrum_status.lean
python3 scripts/spectrum_generate.py --check
```

`Spectrum/AxiomAudit.lean` pins the exact axiom lists of E895, E898, E2789,
and E167. The catalogue asserts complete proof status for all twelve
powers-of-two laws and for E167. These finish all 4630 asserted exact spectra;
64 laws retain mathematically unknown exact spectra.
