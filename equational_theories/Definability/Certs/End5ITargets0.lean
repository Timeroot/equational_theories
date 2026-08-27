import equational_theories.Definability.ExactEnd5I

/-!
# Term-structural certificate targets: `Magma.end5I`

Equations with no model among the `108` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`20` monoid of `Magma.endE5I`. `3` of them are worth listing, of which `3` appear here; each
is a valid *target* `L` of a `Magma.end5I` certificate, and so is not term-structural from any of
the `240` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `108` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`20` monoid
of `Magma.endE5I` satisfies any of these `3` equations. -/
theorem end5I_refutes_0 :
    FamilyRefutes Magma.end5I [
      1285, 2244, 4470
    ] := by nativeDecideFin!
