import equational_theories.Definability.ExactEnd3W

/-!
# Term-structural certificate sources: `Magma.end3W`

For each of the following magmas, drawn from the `21` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`3` monoid of `Magma.endE3W`, the equations it satisfies that no earlier listed
magma does. Together they are the `7` equations that are worth using as the *source* `L'` of a
`Magma.end3W` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `3` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `5` equations satisfied by `Magma.end3W 6`, and by no earlier member of the cover. -/
theorem end3W_satisfies_0 :
    Satisfies (Magma.end3W 6) [
      3675, 3703, 3756, 3823, 4497
    ] := by decide!

/-- `1` equations satisfied by `Magma.end3W 7`, and by no earlier member of the cover. -/
theorem end3W_satisfies_1 :
    Satisfies (Magma.end3W 7) [
      4135
    ] := by decide!

/-- `1` equations satisfied by `Magma.end3W 9`, and by no earlier member of the cover. -/
theorem end3W_satisfies_2 :
    Satisfies (Magma.end3W 9) [
      3414
    ] := by decide!
