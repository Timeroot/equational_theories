import equational_theories.Definability.ExactEnd7C

/-!
# Term-structural certificate targets: `Magma.end7C`

Equations with no model among the `100` magmas on `Fin 7` whose endomorphism monoid is exactly the
order-`25` monoid of `Magma.endE7C`. `8` of them are worth listing, of which `8` appear here; each
is a valid *target* `L` of a `Magma.end7C` certificate, and so is not term-structural from any of
the `19` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd7`.
-/

set_option maxHeartbeats 1000000

/-- None of the `100` magmas on `Fin 7` whose endomorphism monoid is exactly the order-`25` monoid
of `Magma.endE7C` satisfies any of these `8` equations. -/
theorem end7C_refutes_0 :
    FamilyRefutes Magma.end7C [
      105, 221, 326, 375, 3714, 3724, 3749, 3752
    ] := by nativeDecideFin!
