import equational_theories.Definability.ExactEnd6Y

/-!
# Term-structural certificate sources: `Magma.end6Y`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`26` monoid of `Magma.endE6Y`, the equations it satisfies that no earlier listed
magma does. Together they are the `55` equations that are worth using as the *source* `L'` of a
`Magma.end6Y` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `28` equations satisfied by `Magma.end6Y 0`, and by no earlier member of the cover. -/
theorem end6Y_satisfies_0 :
    Satisfies (Magma.end6Y 0) [
      25, 156, 214, 1441, 1644, 1650, 1867, 2259, 2269, 2277, 2285, 2462, 2480, 2484, 2488, 3052,
      3061, 3071, 3093, 3515, 4076, 4124, 4134, 4142, 4150, 4602, 4655, 4675
    ] := by decide!

/-- `27` equations satisfied by `Magma.end6Y 1`, and by no earlier member of the cover. -/
theorem end6Y_satisfies_1 :
    Satisfies (Magma.end6Y 1) [
      10, 110, 153, 422, 426, 432, 450, 454, 458, 1041, 1051, 1059, 1067, 1244, 1262, 1266, 1270,
      1640, 1834, 1853, 2037, 3326, 3338, 3939, 4287, 4340, 4360
    ] := by decide!
