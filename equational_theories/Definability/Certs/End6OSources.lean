import equational_theories.Definability.ExactEnd6O

/-!
# Term-structural certificate sources: `Magma.end6O`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`628` monoid of `Magma.endE6O`, the equations it satisfies that no earlier listed
magma does. Together they are the `34` equations that are worth using as the *source* `L'` of a
`Magma.end6O` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `17` equations satisfied by `Magma.end6O 0`, and by no earlier member of the cover. -/
theorem end6O_satisfies_0 :
    Satisfies (Magma.end6O 0) [
      360, 3662, 3663, 3665, 3666, 3726, 3863, 3866, 4066, 4069, 4072, 4381, 4397, 4401, 4583,
      4597, 4601
    ] := by decide!

/-- `17` equations satisfied by `Magma.end6O 1`, and by no earlier member of the cover. -/
theorem end6O_satisfies_1 :
    Satisfies (Magma.end6O 1) [
      312, 3268, 3274, 3288, 3471, 3491, 3677, 3680, 3684, 3694, 3786, 4272, 4327, 4351, 4452,
      4483, 4494
    ] := by decide!
