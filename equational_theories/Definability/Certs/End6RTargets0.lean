import equational_theories.Definability.ExactEnd6R

/-!
# Term-structural certificate targets: `Magma.end6R`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`52` monoid of `Magma.endE6R`. `10` of them are worth listing, of which `10` appear here; each
is a valid *target* `L` of a `Magma.end6R` certificate, and so is not term-structural from any of
the `57` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`52` monoid of
`Magma.endE6R` satisfies any of these `10` equations. -/
theorem end6R_refutes_0 :
    FamilyRefutes Magma.end6R [
      309, 361, 1637, 1857, 3258, 3459, 3464, 3870, 3887, 4067
    ] := by nativeDecideFin!
