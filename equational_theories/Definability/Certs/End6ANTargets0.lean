import equational_theories.Definability.ExactEnd6AN

/-!
# Term-structural certificate targets: `Magma.end6AN`

Equations with no model among the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`24` monoid of `Magma.endE6AN`. `22` of them are worth listing, of which `22` appear here;
each is a valid *target* `L` of a `Magma.end6AN` certificate, and so is not term-structural from any
of the `4` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`24` monoid of
`Magma.endE6AN` satisfies any of these `22` equations. -/
theorem end6AN_refutes_0 :
    FamilyRefutes Magma.end6AN [
      419, 436, 1038, 1045, 1231, 1241, 1434, 1632, 1921, 2060, 2256, 2263, 2449, 2459, 3058,
      3075, 3261, 3459, 3887, 4073, 4283, 4635
    ] := by nativeDecideFin!
