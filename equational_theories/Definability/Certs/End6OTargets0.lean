import equational_theories.Definability.ExactEnd6O

/-!
# Term-structural certificate targets: `Magma.end6O`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`628` monoid of `Magma.endE6O`. `34` of them are worth listing, of which `34` appear here;
each is a valid *target* `L` of a `Magma.end6O` certificate, and so is not term-structural from any
of the `34` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`628` monoid of
`Magma.endE6O` satisfies any of these `34` equations. -/
theorem end6O_refutes_0 :
    FamilyRefutes Magma.end6O [
      310, 367, 3259, 3262, 3265, 3266, 3462, 3474, 3668, 3687, 3721, 3759, 3868, 3880, 4083,
      4093, 4096, 4104, 4270, 4275, 4307, 4318, 4341, 4383, 4388, 4409, 4433, 4469, 4480, 4585,
      4590, 4611, 4622, 4656
    ] := by nativeDecideFin!
