import equational_theories.Definability.ExactEnd5G

/-!
# Term-structural certificate targets: `Magma.end5G`

Equations with no model among the `2` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`17` monoid of `Magma.endE5G`. `40` of them are worth listing, of which `40` appear here; each
is a valid *target* `L` of a `Magma.end5G` certificate, and so is not term-structural from any of
the `76` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`17` monoid of
`Magma.endE5G` satisfies any of these `40` equations. -/
theorem end5G_refutes_0 :
    FamilyRefutes Magma.end5G [
      10, 25, 104, 205, 323, 378, 426, 427, 429, 439, 832, 833, 1035, 1038, 1048, 1238, 1631,
      1644, 1834, 1847, 2240, 2443, 2459, 2469, 2646, 2699, 3052, 3068, 3078, 3105, 3318, 3519,
      3525, 3529, 3724, 3749, 3925, 3931, 3935, 4155
    ] := by nativeDecideFin!
