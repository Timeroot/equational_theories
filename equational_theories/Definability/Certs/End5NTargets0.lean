import equational_theories.Definability.ExactEnd5N

/-!
# Term-structural certificate targets: `Magma.end5N`

Equations with no model among the `67` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`13` monoid of `Magma.endE5N`. `67` of them are worth listing, of which `67` appear here; each
is a valid *target* `L` of a `Magma.end5N` certificate, and so is not term-structural from any of
the `2` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `67` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`13` monoid of
`Magma.endE5N` satisfies any of these `67` equations. -/
theorem end5N_refutes_0 :
    FamilyRefutes Magma.end5N [
      9, 28, 50, 51, 100, 152, 166, 218, 280, 290, 308, 364, 418, 420, 421, 423, 424, 623, 624,
      626, 627, 820, 821, 823, 1021, 1024, 1224, 1429, 1430, 1478, 1630, 1681, 1701, 1833, 1839,
      1884, 2036, 2124, 2161, 2290, 2493, 2567, 2706, 2733, 2770, 2946, 2956, 2990, 3007, 3122,
      3149, 3159, 3193, 3210, 3256, 3257, 3457, 3533, 3660, 3674, 3877, 3921, 4090, 4268, 4385,
      4395, 4587
    ] := by nativeDecideFin!
