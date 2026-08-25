import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 45 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `19` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `19` equations. -/
theorem exactC45_refutes_44 :
    FamilyRefutes Magma.exactC45 [
      4274, 4281, 4292, 4295, 4298, 4302, 4303, 4306, 4309, 4313, 4322, 4326, 4328, 4329, 4333,
      4335, 4338, 4344, 4345
    ] := by nativeDecideFin!
