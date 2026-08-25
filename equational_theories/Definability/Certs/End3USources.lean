import equational_theories.Definability.ExactEnd3U

/-!
# Term-structural certificate sources: `Magma.end3U`

For each of the following magmas, drawn from the `9` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`5` monoid of `Magma.endE3U`, the equations it satisfies that no earlier listed
magma does. Together they are the `32` equations that are worth using as the *source* `L'` of a
`Magma.end3U` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `5` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `18` equations satisfied by `Magma.end3U 5`, and by no earlier member of the cover. -/
theorem end3U_satisfies_0 :
    Satisfies (Magma.end3U 5) [
      43, 332, 387, 3342, 3545, 3751, 3758, 3964, 4167, 4283, 4358, 4398, 4405, 4442, 4531, 4544,
      4635, 4677
    ] := by decide!

/-- `6` equations satisfied by `Magma.end3U 2`, and by no earlier member of the cover. -/
theorem end3U_satisfies_1 :
    Satisfies (Magma.end3U 2) [
      377, 3927, 4120, 4127, 4293, 4472
    ] := by decide!

/-- `6` equations satisfied by `Magma.end3U 4`, and by no earlier member of the cover. -/
theorem end3U_satisfies_2 :
    Satisfies (Magma.end3U 4) [
      333, 3346, 3353, 3546, 4445, 4658
    ] := by decide!

/-- `1` equations satisfied by `Magma.end3U 0`, and by no earlier member of the cover. -/
theorem end3U_satisfies_3 :
    Satisfies (Magma.end3U 0) [
      4629
    ] := by decide!

/-- `1` equations satisfied by `Magma.end3U 3`, and by no earlier member of the cover. -/
theorem end3U_satisfies_4 :
    Satisfies (Magma.end3U 3) [
      4291
    ] := by decide!
