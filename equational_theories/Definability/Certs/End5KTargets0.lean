import equational_theories.Definability.ExactEnd5K

/-!
# Term-structural certificate targets: `Magma.end5K`

Equations with no model among the `36` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`13` monoid of `Magma.endE5K`. `27` of them are worth listing, of which `27` appear here; each
is a valid *target* `L` of a `Magma.end5K` certificate, and so is not term-structural from any of
the `20` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `36` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`13` monoid of
`Magma.endE5K` satisfies any of these `27` equations. -/
theorem end5K_refutes_0 :
    FamilyRefutes Magma.end5K [
      152, 166, 308, 364, 1428, 1429, 1630, 1681, 1833, 1884, 2050, 2124, 3255, 3256, 3257, 3457,
      3877, 4070, 4090, 4100, 4268, 4282, 4320, 4435, 4587, 4598, 4666
    ] := by nativeDecideFin!
