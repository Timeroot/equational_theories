import equational_theories.Definability.ExactEnd4M

/-!
# Term-structural certificate targets: `Magma.end4M`

Equations with no model among the `2` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`12` monoid of `Magma.endE4M`. `2` of them are worth listing, of which `2` appear here; each
is a valid *target* `L` of a `Magma.end4M` certificate, and so is not term-structural from any of
the `33` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`12` monoid of
`Magma.endE4M` satisfies any of these `2` equations. -/
theorem end4M_refutes_0 :
    FamilyRefutes Magma.end4M [
      3512, 3918
    ] := by nativeDecideFin!
