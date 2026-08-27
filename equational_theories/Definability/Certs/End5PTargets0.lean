import equational_theories.Definability.ExactEnd5P

/-!
# Term-structural certificate targets: `Magma.end5P`

Equations with no model among the `108` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`10` monoid of `Magma.endE5P`. `6` of them are worth listing, of which `6` appear here; each
is a valid *target* `L` of a `Magma.end5P` certificate, and so is not term-structural from any of
the `11` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `108` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`10` monoid
of `Magma.endE5P` satisfies any of these `6` equations. -/
theorem end5P_refutes_0 :
    FamilyRefutes Magma.end5P [
      828, 1457, 2078, 2679, 3533, 3921
    ] := by nativeDecideFin!
