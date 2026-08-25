import equational_theories.Definability.ExactEnd3A

/-!
# Term-structural certificate targets: `Magma.end3A`

Equations with no model among the `1` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`9` monoid of `Magma.endE3A`. `22` of them are worth listing, of which `22` appear here; each
is a valid *target* `L` of a `Magma.end3A` certificate, and so is not term-structural from any of
the `23` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `1` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`9` monoid of
`Magma.endE3A` satisfies any of these `22` equations. -/
theorem end3A_refutes_0 :
    FamilyRefutes Magma.end3A [
      3, 8, 23, 47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238,
      2441, 2644, 2847, 3050
    ] := by nativeDecideFin!
