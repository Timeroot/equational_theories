import equational_theories.Definability.ExactEnd3T

/-!
# Term-structural certificate sources: `Magma.end3T`

For each of the following magmas, drawn from the `6` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`6` monoid of `Magma.endE3T`, the equations it satisfies that no earlier listed
magma does. Together they are the `6` equations that are worth using as the *source* `L'` of a
`Magma.end3T` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `3` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `4` equations satisfied by `Magma.end3T 1`, and by no earlier member of the cover. -/
theorem end3T_satisfies_0 :
    Satisfies (Magma.end3T 1) [
      3555, 3961, 4293, 4658
    ] := by decide!

/-- `1` equations satisfied by `Magma.end3T 0`, and by no earlier member of the cover. -/
theorem end3T_satisfies_1 :
    Satisfies (Magma.end3T 0) [
      2098
    ] := by decide!

/-- `1` equations satisfied by `Magma.end3T 3`, and by no earlier member of the cover. -/
theorem end3T_satisfies_2 :
    Satisfies (Magma.end3T 3) [
      1489
    ] := by decide!
