import equational_theories.Definability.ExactEnd6AC

/-!
# Term-structural certificate targets: `Magma.end6AC`

Equations with no model among the `12` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`882` monoid of `Magma.endE6AC`. `20` of them are worth listing, of which `20` appear here;
each is a valid *target* `L` of a `Magma.end6AC` certificate, and so is not term-structural from any
of the `21` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `12` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`882` monoid
of `Magma.endE6AC` satisfies any of these `20` equations. -/
theorem end6AC_refutes_0 :
    FamilyRefutes Magma.end6AC [
      3322, 3323, 3331, 3334, 3342, 3526, 3534, 3545, 3714, 3752, 3964, 3997, 4023, 4138, 4146,
      4167, 4200, 4226, 4433, 4480
    ] := by nativeDecideFin!
