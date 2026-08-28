import equational_theories.Definability.ExactEnd6X

/-!
# Term-structural certificate targets: `Magma.end6X`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`28` monoid of `Magma.endE6X`. `36` of them are worth listing, of which `36` appear here; each
is a valid *target* `L` of a `Magma.end6X` certificate, and so is not term-structural from any of
the `18` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`28` monoid of
`Magma.endE6X` satisfies any of these `36` equations. -/
theorem end6X_refutes_0 :
    FamilyRefutes Magma.end6X [
      102, 104, 205, 228, 417, 419, 826, 832, 1023, 1029, 1035, 1045, 1226, 1232, 1248, 1258,
      1632, 1634, 1837, 1921, 2246, 2249, 2327, 2337, 2443, 2449, 2530, 2540, 2646, 2743, 3075,
      3112, 3459, 3461, 3864, 3887
    ] := by nativeDecideFin!
