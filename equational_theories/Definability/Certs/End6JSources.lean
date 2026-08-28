import equational_theories.Definability.ExactEnd6J

/-!
# Term-structural certificate sources: `Magma.end6J`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`150` monoid of `Magma.endE6J`, the equations it satisfies that no earlier listed
magma does. Together they are the `82` equations that are worth using as the *source* `L'` of a
`Magma.end6J` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `41` equations satisfied by `Magma.end6J 0`, and by no earlier member of the cover. -/
theorem end6J_satisfies_0 :
    Satisfies (Magma.end6J 0) [
      310, 311, 362, 3260, 3263, 3265, 3266, 3267, 3463, 3466, 3468, 3469, 3470, 3663, 3726,
      3727, 3728, 3730, 3931, 3939, 3947, 4143, 4271, 4285, 4286, 4288, 4289, 4317, 4318, 4319,
      4342, 4359, 4361, 4403, 4436, 4440, 4477, 4506, 4511, 4516, 4521
    ] := by decide!

/-- `41` equations satisfied by `Magma.end6J 2`, and by no earlier member of the cover. -/
theorem end6J_satisfies_1 :
    Satisfies (Magma.end6J 2) [
      315, 367, 370, 3388, 3515, 3529, 3541, 3694, 3732, 3769, 3786, 3837, 3883, 3893, 3901,
      3905, 3909, 4086, 4096, 4104, 4108, 4112, 4391, 4402, 4406, 4412, 4416, 4420, 4424, 4428,
      4593, 4611, 4619, 4625, 4638, 4642, 4649, 4663, 4669, 4682, 4693
    ] := by decide!
