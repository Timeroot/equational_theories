import equational_theories.Definability.ExactEnd4I

/-!
# Term-structural certificate targets: `Magma.end4I`

Equations with no model among the `3` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`10` monoid of `Magma.endE4I`. `19` of them are worth listing, of which `19` appear here; each
is a valid *target* `L` of a `Magma.end4I` certificate, and so is not term-structural from any of
the `40` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `3` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`10` monoid of
`Magma.endE4I` satisfies any of these `19` equations. -/
theorem end4I_refutes_0 :
    FamilyRefutes Magma.end4I [
      325, 385, 3315, 3518, 3521, 3556, 3714, 3752, 3924, 3952, 3962, 4165, 4314, 4399, 4406,
      4433, 4436, 4480, 4606
    ] := by nativeDecideFin!
