import equational_theories.Definability.ExactEnd6V

/-!
# Term-structural certificate sources: `Magma.end6V`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`210` monoid of `Magma.endE6V`, the equations it satisfies that no earlier listed
magma does. Together they are the `64` equations that are worth using as the *source* `L'` of a
`Magma.end6V` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `32` equations satisfied by `Magma.end6V 0`, and by no earlier member of the cover. -/
theorem end6V_satisfies_0 :
    Satisfies (Magma.end6V 0) [
      161, 215, 327, 1458, 1460, 1656, 1659, 1661, 1663, 1852, 1862, 1872, 1874, 2045, 2055,
      2274, 2278, 2286, 2463, 2473, 2477, 2481, 2489, 2656, 2883, 3321, 3324, 3520, 3527, 3669,
      3716, 3930
    ] := by decide!

/-- `32` equations satisfied by `Magma.end6V 1`, and by no earlier member of the cover. -/
theorem end6V_satisfies_1 :
    Satisfies (Magma.end6V 1) [
      138, 194, 395, 690, 960, 1096, 1133, 1150, 1167, 1202, 1299, 1336, 1405, 1560, 1586, 1742,
      1763, 1797, 1816, 1912, 1979, 2000, 2024, 2182, 2227, 3566, 3702, 3790, 4006, 4040, 4175,
      4243
    ] := by decide!
