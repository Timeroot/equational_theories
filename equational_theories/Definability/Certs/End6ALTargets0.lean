import equational_theories.Definability.ExactEnd6AL

/-!
# Term-structural certificate targets: `Magma.end6AL`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`42` monoid of `Magma.endE6AL`. `18` of them are worth listing, of which `18` appear here;
each is a valid *target* `L` of a `Magma.end6AL` certificate, and so is not term-structural from any
of the `2` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`42` monoid of
`Magma.endE6AL` satisfies any of these `18` equations. -/
theorem end6AL_refutes_0 :
    FamilyRefutes Magma.end6AL [
      107, 211, 323, 378, 1048, 1241, 1251, 1644, 1834, 2256, 2266, 2469, 3255, 3519, 3925, 4070,
      4269, 4584
    ] := by nativeDecideFin!
