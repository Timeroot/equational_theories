import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 31 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `20` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `20` equations. -/
theorem exactC45_refutes_30 :
    FamilyRefutes Magma.exactC45 [
      3991, 3992, 3995, 3996, 3998, 3999, 4000, 4002, 4003, 4004, 4005, 4008, 4009, 4011, 4012,
      4015, 4016, 4017, 4019, 4020
    ] := by nativeDecideFin!
