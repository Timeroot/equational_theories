import equational_theories.Definability.ExactEnd6AH

/-!
# Term-structural certificate targets: `Magma.end6AH`

Equations with no model among the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`28` monoid of `Magma.endE6AH`. `16` of them are worth listing, of which `16` appear here;
each is a valid *target* `L` of a `Magma.end6AH` certificate, and so is not term-structural from any
of the `2` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`28` monoid of
`Magma.endE6AH` satisfies any of these `16` equations. -/
theorem end6AH_refutes_0 :
    FamilyRefutes Magma.end6AH [
      104, 205, 1025, 1035, 1228, 1248, 1631, 1634, 1837, 1847, 2243, 2246, 2443, 2446, 3458, 3867
    ] := by nativeDecideFin!
