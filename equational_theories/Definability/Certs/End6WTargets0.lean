import equational_theories.Definability.ExactEnd6W

/-!
# Term-structural certificate targets: `Magma.end6W`

Equations with no model among the `16` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`32` monoid of `Magma.endE6W`. `42` of them are worth listing, of which `42` appear here; each
is a valid *target* `L` of a `Magma.end6W` certificate, and so is not term-structural from any of
the `28` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `16` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`32` monoid of
`Magma.endE6W` satisfies any of these `42` equations. -/
theorem end6W_refutes_0 :
    FamilyRefutes Magma.end6W [
      10, 25, 107, 211, 326, 375, 413, 416, 419, 426, 1038, 1048, 1241, 1251, 1441, 1654, 1840,
      2037, 2256, 2266, 2459, 2469, 3052, 3055, 3065, 3075, 3318, 3322, 3343, 3346, 3462, 3525,
      3880, 3935, 4120, 4130, 4138, 4155, 4291, 4320, 4598, 4629
    ] := by nativeDecideFin!
