import equational_theories.Definability.ExactEnd6AD

/-!
# Term-structural certificate targets: `Magma.end6AD`

Equations with no model among the `12` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`141` monoid of `Magma.endE6AD`. `40` of them are worth listing, of which `40` appear here;
each is a valid *target* `L` of a `Magma.end6AD` certificate, and so is not term-structural from any
of the `11` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `12` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`141` monoid
of `Magma.endE6AD` satisfies any of these `40` equations. -/
theorem end6AD_refutes_0 :
    FamilyRefutes Magma.end6AD [
      10, 25, 110, 214, 323, 378, 413, 426, 427, 432, 630, 906, 1038, 1041, 1048, 1051, 1059,
      1063, 1266, 1644, 1650, 1834, 1853, 2269, 2459, 2462, 2469, 2472, 2480, 2484, 2647, 2902,
      3052, 3065, 3071, 3105, 3322, 3521, 3952, 4138
    ] := by nativeDecideFin!
