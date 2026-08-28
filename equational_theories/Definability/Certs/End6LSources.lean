import equational_theories.Definability.ExactEnd6L

/-!
# Term-structural certificate sources: `Magma.end6L`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`35` monoid of `Magma.endE6L`, the equations it satisfies that no earlier listed
magma does. Together they are the `58` equations that are worth using as the *source* `L'` of a
`Magma.end6L` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `29` equations satisfied by `Magma.end6L 0`, and by no earlier member of the cover. -/
theorem end6L_satisfies_0 :
    Satisfies (Magma.end6L 0) [
      427, 430, 433, 434, 442, 443, 833, 834, 837, 839, 840, 854, 1042, 1052, 1060, 1230, 1243,
      1259, 1260, 1851, 1855, 1863, 3279, 3285, 3881, 3888, 3894, 3902, 4318
    ] := by decide!

/-- `29` equations satisfied by `Magma.end6L 1`, and by no earlier member of the cover. -/
theorem end6L_satisfies_1 :
    Satisfies (Magma.end6L 1) [
      1672, 1721, 1724, 2306, 2310, 2314, 2372, 2554, 2571, 2588, 2699, 2702, 2712, 2739, 2774,
      2778, 3093, 3105, 3142, 3145, 3180, 3197, 3475, 3482, 3488, 3496, 4084, 4105, 4611
    ] := by decide!
