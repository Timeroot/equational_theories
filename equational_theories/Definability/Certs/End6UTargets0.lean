import equational_theories.Definability.ExactEnd6U

/-!
# Term-structural certificate targets: `Magma.end6U`

Equations with no model among the `14` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`18` monoid of `Magma.endE6U`. `11` of them are worth listing, of which `11` appear here; each
is a valid *target* `L` of a `Magma.end6U` certificate, and so is not term-structural from any of
the `45` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `14` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`18` monoid of
`Magma.endE6U` satisfies any of these `11` equations. -/
theorem end6U_refutes_0 :
    FamilyRefutes Magma.end6U [
      1053, 2558, 3459, 3481, 3489, 3714, 3752, 3865, 3887, 3895, 4544
    ] := by nativeDecideFin!
