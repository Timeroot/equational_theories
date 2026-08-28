import equational_theories.Definability.ExactEnd6K

/-!
# Term-structural certificate targets: `Magma.end6K`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`80` monoid of `Magma.endE6K`. `16` of them are worth listing, of which `16` appear here; each
is a valid *target* `L` of a `Magma.end6K` certificate, and so is not term-structural from any of
the `133` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`80` monoid of
`Magma.endE6K` satisfies any of these `16` equations. -/
theorem end6K_refutes_0 :
    FamilyRefutes Magma.end6K [
      101, 208, 1022, 1028, 1225, 1231, 1434, 2060, 2253, 2263, 2456, 2466, 3461, 3512, 3864, 3918
    ] := by nativeDecideFin!
