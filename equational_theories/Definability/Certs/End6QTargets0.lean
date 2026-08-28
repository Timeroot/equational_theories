import equational_theories.Definability.ExactEnd6Q

/-!
# Term-structural certificate targets: `Magma.end6Q`

Equations with no model among the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`70` monoid of `Magma.endE6Q`. `52` of them are worth listing, of which `52` appear here; each
is a valid *target* `L` of a `Magma.end6Q` certificate, and so is not term-structural from any of
the `34` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`70` monoid of
`Magma.endE6Q` satisfies any of these `52` equations. -/
theorem end6Q_refutes_0 :
    FamilyRefutes Magma.end6Q [
      307, 310, 312, 316, 359, 360, 367, 368, 3258, 3262, 3266, 3268, 3272, 3456, 3458, 3461,
      3464, 3472, 3475, 3482, 3485, 3500, 3660, 3661, 3664, 3668, 3674, 3678, 3685, 3687, 3862,
      3864, 3867, 3870, 3878, 3881, 3888, 3891, 3906, 4066, 4067, 4091, 4093, 4096, 4272, 4276,
      4321, 4343, 4583, 4591, 4608, 4636
    ] := by nativeDecideFin!
