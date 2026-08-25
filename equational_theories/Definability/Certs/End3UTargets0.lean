import equational_theories.Definability.ExactEnd3U

/-!
# Term-structural certificate targets: `Magma.end3U`

Equations with no model among the `9` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`5` monoid of `Magma.endE3U`. `10` of them are worth listing, of which `10` appear here; each
is a valid *target* `L` of a `Magma.end3U` certificate, and so is not term-structural from any of
the `32` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `9` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`5` monoid of
`Magma.endE3U` satisfies any of these `10` equations. -/
theorem end3U_refutes_0 :
    FamilyRefutes Magma.end3U [
      3315, 3316, 3518, 3556, 3924, 3962, 4128, 4165, 4314, 4606
    ] := by nativeDecideFin!
