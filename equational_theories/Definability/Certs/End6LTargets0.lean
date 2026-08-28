import equational_theories.Definability.ExactEnd6L

/-!
# Term-structural certificate targets: `Magma.end6L`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`35` monoid of `Magma.endE6L`. `94` of them are worth listing, of which `94` appear here; each
is a valid *target* `L` of a `Magma.end6L` certificate, and so is not term-structural from any of
the `58` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`35` monoid of
`Magma.endE6L` satisfies any of these `94` equations. -/
theorem end6L_refutes_0 :
    FamilyRefutes Magma.end6L [
      111, 242, 309, 313, 319, 361, 365, 371, 838, 1053, 1056, 1068, 1245, 1263, 1264, 1265,
      1267, 1271, 2351, 2368, 2389, 2402, 2420, 2425, 2517, 2558, 2623, 2665, 3259, 3261, 3264,
      3265, 3269, 3271, 3274, 3275, 3289, 3290, 3294, 3297, 3301, 3302, 3459, 3467, 3478, 3481,
      3489, 3492, 3504, 3529, 3865, 3873, 3884, 3887, 3895, 3898, 3910, 3931, 4071, 4072, 4073,
      4076, 4081, 4083, 4085, 4087, 4101, 4104, 4106, 4107, 4109, 4113, 4273, 4279, 4320, 4324,
      4325, 4327, 4331, 4332, 4336, 4337, 4362, 4588, 4594, 4598, 4601, 4616, 4620, 4626, 4639,
      4647, 4651, 4673
    ] := by nativeDecideFin!
