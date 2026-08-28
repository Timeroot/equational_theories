import equational_theories.Definability.ExactEnd6J

/-!
# Term-structural certificate targets: `Magma.end6J`

Equations with no model among the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`150` monoid of `Magma.endE6J`. `95` of them are worth listing, of which `95` appear here;
each is a valid *target* `L` of a `Magma.end6J` certificate, and so is not term-structural from any
of the `82` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`150` monoid of
`Magma.endE6J` satisfies any of these `95` equations. -/
theorem end6J_refutes_0 :
    FamilyRefutes Magma.end6J [
      312, 323, 360, 378, 3268, 3274, 3281, 3284, 3288, 3296, 3309, 3326, 3343, 3471, 3474, 3477,
      3481, 3484, 3487, 3491, 3499, 3511, 3518, 3549, 3665, 3666, 3667, 3668, 3671, 3672, 3677,
      3680, 3687, 3690, 3698, 3863, 3865, 3866, 3868, 3869, 3871, 3872, 3875, 3917, 3955, 3962,
      4066, 4069, 4072, 4074, 4075, 4078, 4121, 4130, 4134, 4272, 4291, 4300, 4304, 4327, 4330,
      4351, 4374, 4381, 4397, 4398, 4400, 4401, 4433, 4434, 4435, 4442, 4445, 4452, 4460, 4470,
      4471, 4472, 4475, 4476, 4480, 4483, 4486, 4494, 4498, 4508, 4533, 4583, 4597, 4601, 4603,
      4629, 4630, 4654, 4672
    ] := by nativeDecideFin!
