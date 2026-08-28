import equational_theories.Definability.ExactEnd6H

/-!
# Term-structural certificate targets: `Magma.end6H`

Equations with no model among the `16` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`70` monoid of `Magma.endE6H`. `110` of them are worth listing, of which `110` appear here;
each is a valid *target* `L` of a `Magma.end6H` certificate, and so is not term-structural from any
of the `106` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `16` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`70` monoid of
`Magma.endE6H` satisfies any of these `110` equations. -/
theorem end6H_refutes_0 :
    FamilyRefutes Magma.end6H [
      315, 325, 326, 362, 375, 385, 3271, 3274, 3281, 3284, 3296, 3308, 3309, 3315, 3318, 3319,
      3322, 3323, 3331, 3334, 3346, 3509, 3515, 3518, 3519, 3520, 3521, 3522, 3523, 3525, 3526,
      3529, 3533, 3534, 3537, 3541, 3546, 3556, 3665, 3666, 3667, 3668, 3671, 3672, 3677, 3680,
      3687, 3690, 3698, 3714, 3752, 3915, 3921, 3924, 3925, 3927, 3928, 3931, 3935, 3939, 3943,
      3947, 3952, 3962, 3989, 3997, 4006, 4023, 4071, 4072, 4074, 4075, 4078, 4118, 4120, 4121,
      4138, 4146, 4155, 4158, 4165, 4200, 4226, 4275, 4304, 4307, 4320, 4327, 4362, 4383, 4406,
      4409, 4424, 4435, 4436, 4437, 4445, 4460, 4472, 4474, 4475, 4477, 4529, 4546, 4585, 4598,
      4601, 4603, 4656, 4673
    ] := by nativeDecideFin!
