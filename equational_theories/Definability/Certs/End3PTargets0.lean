import equational_theories.Definability.ExactEnd3P

/-!
# Term-structural certificate targets: `Magma.end3P`

Equations with no model among the `12` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`5` monoid of `Magma.endE3P`. `94` of them are worth listing, of which `94` appear here; each
is a valid *target* `L` of a `Magma.end3P` certificate, and so is not term-structural from any of
the `128` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `12` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`5` monoid of
`Magma.endE3P` satisfies any of these `94` equations. -/
theorem end3P_refutes_0 :
    FamilyRefutes Magma.end3P [
      47, 151, 255, 315, 362, 430, 455, 658, 836, 843, 1249, 1444, 1635, 1684, 1721, 1848, 1851,
      1894, 2053, 2303, 2709, 2736, 3011, 3142, 3214, 3263, 3281, 3284, 3296, 3308, 3309, 3343,
      3463, 3465, 3466, 3468, 3469, 3477, 3484, 3487, 3499, 3512, 3533, 3556, 3671, 3698, 3869,
      3871, 3872, 3875, 3883, 3890, 3893, 3901, 3905, 3918, 3921, 3924, 4074, 4075, 4078, 4108,
      4121, 4130, 4158, 4283, 4284, 4286, 4288, 4291, 4296, 4304, 4358, 4412, 4434, 4435, 4438,
      4440, 4445, 4460, 4470, 4471, 4472, 4475, 4486, 4498, 4599, 4603, 4619, 4629, 4633, 4635,
      4642, 4677
    ] := by nativeDecideFin!
