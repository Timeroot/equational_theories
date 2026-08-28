import equational_theories.Definability.ExactEnd6V

/-!
# Term-structural certificate targets: `Magma.end6V`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`210` monoid of `Magma.endE6V`. `4` of them are worth listing, of which `4` appear here; each
is a valid *target* `L` of a `Magma.end6V` certificate, and so is not term-structural from any of
the `64` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`210` monoid of
`Magma.endE6V` satisfies any of these `4` equations. -/
theorem end6V_refutes_0 :
    FamilyRefutes Magma.end6V [
      562, 3091, 4362, 4673
    ] := by nativeDecideFin!
