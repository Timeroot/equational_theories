import equational_theories.Definability.ExactEnd3O

/-!
# Term-structural certificate sources: `Magma.end3O`

For each of the following magmas, drawn from the `5` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`5` monoid of `Magma.endE3O`, the equations it satisfies that no earlier listed
magma does. Together they are the `68` equations that are worth using as the *source* `L'` of a
`Magma.end3O` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `68` equations satisfied by `Magma.end3O 0`, and by no earlier member of the cover. -/
theorem end3O_satisfies_0 :
    Satisfies (Magma.end3O 0) [
      43, 323, 325, 332, 333, 377, 378, 385, 387, 3316, 3318, 3342, 3345, 3346, 3353, 3355, 3512,
      3519, 3545, 3546, 3548, 3555, 3556, 3751, 3758, 3918, 3924, 3925, 3927, 3954, 3961, 3964,
      4120, 4127, 4128, 4154, 4155, 4157, 4167, 4283, 4291, 4293, 4321, 4343, 4358, 4362, 4364,
      4398, 4405, 4406, 4436, 4442, 4443, 4445, 4472, 4512, 4515, 4525, 4531, 4541, 4544, 4629,
      4635, 4636, 4658, 4673, 4677, 4679
    ] := by decide!
