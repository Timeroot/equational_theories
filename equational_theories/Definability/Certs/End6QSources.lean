import equational_theories.Definability.ExactEnd6Q

/-!
# Term-structural certificate sources: `Magma.end6Q`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`70` monoid of `Magma.endE6Q`, the equations it satisfies that no earlier listed
magma does. Together they are the `34` equations that are worth using as the *source* `L'` of a
`Magma.end6Q` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `34` equations satisfied by `Magma.end6Q 1`, and by no earlier member of the cover. -/
theorem end6Q_satisfies_0 :
    Satisfies (Magma.end6Q 1) [
      1, 40, 3253, 3255, 3256, 3279, 3282, 3285, 3286, 3306, 3662, 3665, 3677, 3684, 3688, 3692,
      3700, 4070, 4084, 4094, 4098, 4105, 4131, 4269, 4270, 4314, 4316, 4318, 4341, 4584, 4590,
      4611, 4622, 4631
    ] := by decide!
