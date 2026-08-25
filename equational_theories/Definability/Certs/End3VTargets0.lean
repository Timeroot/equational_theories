import equational_theories.Definability.ExactEnd3V

/-!
# Term-structural certificate targets: `Magma.end3V`

Equations with no model among the `2` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`6` monoid of `Magma.endE3V`. `11` of them are worth listing, of which `11` appear here; each
is a valid *target* `L` of a `Magma.end3V` certificate, and so is not term-structural from any of
the `18` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`6` monoid of
`Magma.endE3V` satisfies any of these `11` equations. -/
theorem end3V_refutes_0 :
    FamilyRefutes Magma.end3V [
      3318, 3519, 3724, 3749, 3925, 4155, 4314, 4343, 4435, 4606, 4608
    ] := by nativeDecideFin!
