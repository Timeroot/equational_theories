import equational_theories.Definability.ExactEnd6Z

/-!
# Term-structural certificate targets: `Magma.end6Z`

Equations with no model among the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`36` monoid of `Magma.endE6Z`. `20` of them are worth listing, of which `20` appear here; each
is a valid *target* `L` of a `Magma.end6Z` certificate, and so is not term-structural from any of
the `15` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`36` monoid of
`Magma.endE6Z` satisfies any of these `20` equations. -/
theorem end6Z_refutes_0 :
    FamilyRefutes Magma.end6Z [
      104, 205, 429, 1035, 1045, 1238, 1248, 1258, 1451, 2043, 2240, 2246, 2249, 2443, 2449,
      3068, 3458, 3519, 3867, 3925
    ] := by nativeDecideFin!
