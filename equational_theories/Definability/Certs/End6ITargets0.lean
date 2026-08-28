import equational_theories.Definability.ExactEnd6I

/-!
# Term-structural certificate targets: `Magma.end6I`

Equations with no model among the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`28` monoid of `Magma.endE6I`. `44` of them are worth listing, of which `44` appear here; each
is a valid *target* `L` of a `Magma.end6I` certificate, and so is not term-structural from any of
the `93` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`28` monoid of
`Magma.endE6I` satisfies any of these `44` equations. -/
theorem end6I_refutes_0 :
    FamilyRefutes Magma.end6I [
      309, 310, 312, 360, 361, 367, 3258, 3259, 3261, 3262, 3266, 3268, 3278, 3288, 3306, 3458,
      3459, 3467, 3661, 3663, 3664, 3694, 3867, 3873, 3887, 4066, 4067, 4068, 4069, 4073, 4083,
      4093, 4096, 4131, 4269, 4272, 4314, 4316, 4351, 4583, 4584, 4597, 4606, 4631
    ] := by nativeDecideFin!
