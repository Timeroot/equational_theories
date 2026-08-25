import equational_theories.Definability.ExactEnd3W

/-!
# Term-structural certificate targets: `Magma.end3W`

Equations with no model among the `21` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`3` monoid of `Magma.endE3W`. `8` of them are worth listing, of which `8` appear here; each is
a valid *target* `L` of a `Magma.end3W` certificate, and so is not term-structural from any of the
`7` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `21` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`3` monoid of
`Magma.endE3W` satisfies any of these `8` equations. -/
theorem end3W_refutes_0 :
    FamilyRefutes Magma.end3W [
      3334, 3346, 3474, 3526, 3868, 4023, 4120, 4146
    ] := by nativeDecideFin!
