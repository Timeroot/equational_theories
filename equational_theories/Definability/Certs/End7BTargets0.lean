import equational_theories.Definability.ExactEnd7B

/-!
# Term-structural certificate targets: `Magma.end7B`

Equations with no model among the `38` magmas on `Fin 7` whose endomorphism monoid is exactly the
order-`223` monoid of `Magma.endE7B`. `14` of them are worth listing, of which `14` appear here;
each is a valid *target* `L` of a `Magma.end7B` certificate, and so is not term-structural from any
of the `14` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd7`.
-/

set_option maxHeartbeats 1000000

/-- None of the `38` magmas on `Fin 7` whose endomorphism monoid is exactly the order-`223` monoid
of `Magma.endE7B` satisfies any of these `14` equations. -/
theorem end7B_refutes_0 :
    FamilyRefutes Magma.end7B [
      104, 205, 832, 1035, 1045, 1238, 1248, 2240, 2246, 2443, 2449, 2646, 3461, 3864
    ] := by nativeDecideFin!
