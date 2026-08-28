import equational_theories.Definability.ExactEnd6AM

/-!
# Term-structural certificate sources: `Magma.end6AM`

For each of the following magmas, drawn from the `6` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`20` monoid of `Magma.endE6AM`, the equations it satisfies that no earlier listed
magma does. Together they are the `18` equations that are worth using as the *source* `L'` of a
`Magma.end6AM` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `8` equations satisfied by `Magma.end6AM 0`, and by no earlier member of the cover. -/
theorem end6AM_satisfies_0 :
    Satisfies (Magma.end6AM 0) [
      325, 3317, 3666, 3866, 4072, 4397, 4401, 4601
    ] := by decide!

/-- `8` equations satisfied by `Magma.end6AM 1`, and by no earlier member of the cover. -/
theorem end6AM_satisfies_1 :
    Satisfies (Magma.end6AM 1) [
      385, 3274, 3491, 3680, 4209, 4327, 4452, 4494
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AM 2`, and by no earlier member of the cover. -/
theorem end6AM_satisfies_2 :
    Satisfies (Magma.end6AM 2) [
      1055
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AM 3`, and by no earlier member of the cover. -/
theorem end6AM_satisfies_3 :
    Satisfies (Magma.end6AM 3) [
      2452
    ] := by decide!
