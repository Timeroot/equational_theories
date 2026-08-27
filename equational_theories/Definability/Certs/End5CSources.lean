import equational_theories.Definability.ExactEnd5C

/-!
# Term-structural certificate sources: `Magma.end5C`

For each of the following magmas, drawn from the `4` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`17` monoid of `Magma.endE5C`, the equations it satisfies that no earlier listed
magma does. Together they are the `64` equations that are worth using as the *source* `L'` of a
`Magma.end5C` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `33` equations satisfied by `Magma.end5C 0`, and by no earlier member of the cover. -/
theorem end5C_satisfies_0 :
    Satisfies (Magma.end5C 0) [
      48, 101, 102, 412, 413, 414, 415, 615, 616, 617, 618, 818, 822, 826, 827, 1022, 1025, 1028,
      1029, 1031, 1032, 1225, 1228, 1234, 1427, 1631, 1632, 1655, 2240, 2446, 3254, 3318, 3458
    ] := by decide!

/-- `31` equations satisfied by `Magma.end5C 2`, and by no earlier member of the cover. -/
theorem end5C_satisfies_1 :
    Satisfies (Magma.end5C 2) [
      208, 228, 270, 1238, 1847, 1897, 1921, 2087, 2243, 2253, 2273, 2456, 2466, 2476, 2540,
      2584, 2649, 2696, 2743, 2804, 2862, 2899, 2936, 2973, 3065, 3102, 3139, 3176, 3867, 4080,
      4155
    ] := by decide!
