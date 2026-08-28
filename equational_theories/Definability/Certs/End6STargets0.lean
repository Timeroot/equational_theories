import equational_theories.Definability.ExactEnd6S

/-!
# Term-structural certificate targets: `Magma.end6S`

Equations with no model among the `24` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`30` monoid of `Magma.endE6S`. `66` of them are worth listing, of which `66` appear here; each
is a valid *target* `L` of a `Magma.end6S` certificate, and so is not term-structural from any of
the `50` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `24` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`30` monoid of
`Magma.endE6S` satisfies any of these `66` equations. -/
theorem end6S_refutes_0 :
    FamilyRefutes Magma.end6S [
      309, 310, 311, 361, 367, 370, 3260, 3262, 3263, 3265, 3266, 3326, 3464, 3465, 3466, 3467,
      3468, 3469, 3509, 3520, 3526, 3870, 3873, 3890, 3893, 3901, 3905, 3928, 4006, 4023, 4086,
      4093, 4096, 4104, 4108, 4134, 4270, 4271, 4272, 4283, 4285, 4286, 4287, 4288, 4291, 4300,
      4317, 4318, 4320, 4330, 4340, 4341, 4351, 4358, 4362, 4583, 4590, 4593, 4597, 4598, 4602,
      4629, 4635, 4642, 4673, 4677
    ] := by nativeDecideFin!
