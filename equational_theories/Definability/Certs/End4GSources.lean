import equational_theories.Definability.ExactEnd4G

/-!
# Term-structural certificate sources: `Magma.end4G`

For each of the following magmas, drawn from the `24` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`8` monoid of `Magma.endE4G`, the equations it satisfies that no earlier listed
magma does. Together they are the `58` equations that are worth using as the *source* `L'` of a
`Magma.end4G` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `3` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `40` equations satisfied by `Magma.end4G 1`, and by no earlier member of the cover. -/
theorem end4G_satisfies_0 :
    Satisfies (Magma.end4G 1) [
      101, 104, 205, 208, 419, 616, 619, 632, 822, 832, 1022, 1025, 1031, 1035, 1228, 1238, 1258,
      1444, 1631, 1634, 1837, 1847, 2053, 2240, 2243, 2249, 2443, 2446, 2456, 2476, 2646, 2649,
      2852, 2862, 2865, 3075, 3458, 3461, 3864, 3867
    ] := by decide!

/-- `9` equations satisfied by `Magma.end4G 0`, and by no earlier member of the cover. -/
theorem end4G_satisfies_1 :
    Satisfies (Magma.end4G 0) [
      48, 412, 413, 414, 415, 615, 818, 1427, 3254
    ] := by decide!

/-- `9` equations satisfied by `Magma.end4G 5`, and by no earlier member of the cover. -/
theorem end4G_satisfies_2 :
    Satisfies (Magma.end4G 5) [
      270, 2087, 2696, 2899, 3065, 3102, 3139, 3176, 4080
    ] := by decide!
