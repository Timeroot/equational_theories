import equational_theories.Definability.ExactEnd5W

/-!
# Term-structural certificate targets: `Magma.end5W`

Equations with no model among the `1` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`10` monoid of `Magma.endE5W`. `47` of them are worth listing, of which `47` appear here; each
is a valid *target* `L` of a `Magma.end5W` certificate, and so is not term-structural from any of
the `6` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `1` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`10` monoid of
`Magma.endE5W` satisfies any of these `47` equations. -/
theorem end5W_refutes_0 :
    FamilyRefutes Magma.end5W [
      11, 31, 414, 436, 440, 820, 823, 835, 842, 1028, 1036, 1049, 1226, 1248, 1252, 1637, 1718,
      1835, 1857, 2246, 2327, 2340, 2466, 2496, 2543, 2652, 2662, 2706, 2733, 3058, 3139, 3152,
      3256, 3464, 3472, 3659, 3662, 3684, 3712, 3721, 3725, 3759, 3870, 3878, 4090, 4270, 4590
    ] := by nativeDecideFin!
