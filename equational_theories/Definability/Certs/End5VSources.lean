import equational_theories.Definability.ExactEnd5V

/-!
# Term-structural certificate sources: `Magma.end5V`

For each of the following magmas, drawn from the `16` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`29` monoid of `Magma.endE5V`, the equations it satisfies that no earlier listed
magma does. Together they are the `25` equations that are worth using as the *source* `L'` of a
`Magma.end5V` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `3` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `19` equations satisfied by `Magma.end5V 0`, and by no earlier member of the cover. -/
theorem end5V_satisfies_0 :
    Satisfies (Magma.end5V 0) [
      325, 335, 384, 385, 3318, 3345, 3519, 3548, 3555, 3714, 3748, 3751, 3752, 3761, 3925, 3954,
      3961, 4155, 4157
    ] := by decide!

/-- `3` equations satisfied by `Magma.end5V 1`, and by no earlier member of the cover. -/
theorem end5V_satisfies_1 :
    Satisfies (Magma.end5V 1) [
      3520, 3926, 4437
    ] := by decide!

/-- `3` equations satisfied by `Magma.end5V 4`, and by no earlier member of the cover. -/
theorem end5V_satisfies_2 :
    Satisfies (Magma.end5V 4) [
      3600, 4006, 4546
    ] := by decide!
