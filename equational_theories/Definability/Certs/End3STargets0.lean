import equational_theories.Definability.ExactEnd3S

/-!
# Term-structural certificate targets: `Magma.end3S`

Equations with no model among the `3` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`5` monoid of `Magma.endE3S`. `40` of them are worth listing, of which `40` appear here; each
is a valid *target* `L` of a `Magma.end3S` certificate, and so is not term-structural from any of
the `60` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `3` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`5` monoid of
`Magma.endE3S` satisfies any of these `40` equations. -/
theorem end3S_refutes_0 :
    FamilyRefutes Magma.end3S [
      3334, 3414, 3457, 3465, 3471, 3484, 3526, 3863, 3871, 3877, 3890, 4023, 4135, 4146, 4275,
      4290, 4293, 4297, 4307, 4381, 4383, 4386, 4389, 4396, 4408, 4409, 4424, 4433, 4446, 4470,
      4473, 4477, 4479, 4480, 4483, 4585, 4605, 4612, 4656, 4658
    ] := by nativeDecideFin!
