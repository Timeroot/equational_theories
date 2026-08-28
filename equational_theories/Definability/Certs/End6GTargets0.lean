import equational_theories.Definability.ExactEnd6G

/-!
# Term-structural certificate targets: `Magma.end6G`

Equations with no model among the `3` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`100` monoid of `Magma.endE6G`. `52` of them are worth listing, of which `52` appear here;
each is a valid *target* `L` of a `Magma.end6G` certificate, and so is not term-structural from any
of the `219` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `3` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`100` monoid of
`Magma.endE6G` satisfies any of these `52` equations. -/
theorem end6G_refutes_0 :
    FamilyRefutes Magma.end6G [
      3319, 3353, 3509, 3522, 3915, 3928, 4118, 4127, 4401, 4406, 4412, 4417, 4421, 4429, 4436,
      4437, 4438, 4439, 4440, 4441, 4443, 4444, 4448, 4449, 4450, 4451, 4452, 4453, 4454, 4455,
      4456, 4457, 4458, 4459, 4464, 4465, 4466, 4467, 4468, 4510, 4514, 4518, 4524, 4532, 4536,
      4542, 4546, 4554, 4560, 4565, 4570, 4580
    ] := by nativeDecideFin!
