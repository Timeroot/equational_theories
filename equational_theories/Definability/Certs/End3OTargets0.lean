import equational_theories.Definability.ExactEnd3O

/-!
# Term-structural certificate targets: `Magma.end3O`

Equations with no model among the `5` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`5` monoid of `Magma.endE3O`. `131` of them are worth listing, of which `131` appear here;
each is a valid *target* `L` of a `Magma.end3O` certificate, and so is not term-structural from any
of the `68` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `5` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`5` monoid of
`Magma.endE3O` satisfies any of these `131` equations. -/
theorem end3O_refutes_0 :
    FamilyRefutes Magma.end3O [
      308, 309, 310, 312, 360, 361, 364, 367, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3264,
      3265, 3266, 3268, 3271, 3274, 3278, 3288, 3321, 3322, 3323, 3331, 3334, 3414, 3457, 3458,
      3459, 3461, 3462, 3464, 3465, 3467, 3474, 3481, 3484, 3525, 3526, 3529, 3534, 3537, 3660,
      3661, 3662, 3663, 3664, 3665, 3667, 3668, 3672, 3674, 3677, 3684, 3687, 3690, 3694, 3729,
      3820, 3864, 3865, 3867, 3868, 3870, 3871, 3873, 3877, 3880, 3887, 3890, 3931, 3935, 3943,
      3997, 4023, 4066, 4067, 4068, 4069, 4070, 4071, 4072, 4073, 4076, 4080, 4083, 4090, 4093,
      4096, 4104, 4135, 4138, 4146, 4175, 4200, 4226, 4268, 4269, 4270, 4272, 4275, 4307, 4316,
      4318, 4327, 4341, 4351, 4382, 4383, 4385, 4388, 4395, 4409, 4424, 4432, 4469, 4477, 4583,
      4584, 4585, 4587, 4590, 4597, 4601, 4611, 4622, 4631, 4656
    ] := by nativeDecideFin!
