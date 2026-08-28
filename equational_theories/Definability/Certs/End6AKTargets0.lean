import equational_theories.Definability.ExactEnd6AK

/-!
# Term-structural certificate targets: `Magma.end6AK`

Equations with no model among the `1` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`63` monoid of `Magma.endE6AK`. `4` of them are worth listing, of which `4` appear here; each
is a valid *target* `L` of a `Magma.end6AK` certificate, and so is not term-structural from any of
the `13` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `1` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`63` monoid of
`Magma.endE6AK` satisfies any of these `4` equations. -/
theorem end6AK_refutes_0 :
    FamilyRefutes Magma.end6AK [
      3306, 3353, 4127, 4131
    ] := by nativeDecideFin!
