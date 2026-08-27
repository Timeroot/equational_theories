import equational_theories.Definability.ExactEnd5J

/-!
# Term-structural certificate targets: `Magma.end5J`

Equations with no model among the `23` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`17` monoid of `Magma.endE5J`. `44` of them are worth listing, of which `44` appear here; each
is a valid *target* `L` of a `Magma.end5J` certificate, and so is not term-structural from any of
the `114` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `23` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`17` monoid of
`Magma.endE5J` satisfies any of these `44` equations. -/
theorem end5J_refutes_0 :
    FamilyRefutes Magma.end5J [
      53, 273, 422, 442, 446, 450, 454, 455, 458, 617, 630, 639, 643, 647, 658, 1442, 1445, 1481,
      1515, 1684, 1694, 1848, 1858, 2038, 2051, 2090, 2127, 2855, 2902, 2936, 2949, 2964, 3011,
      3061, 3081, 3085, 3089, 3093, 3097, 3214, 3549, 3556, 3917, 3924
    ] := by nativeDecideFin!
