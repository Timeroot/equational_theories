import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 37 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `25` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `25` equations. -/
theorem exactC45_refutes_36 :
    FamilyRefutes Magma.exactC45 [
      4079, 4089, 4103, 4116, 4117, 4119, 4122, 4123, 4125, 4126, 4129, 4132, 4133, 4136, 4137,
      4139, 4140, 4141, 4144, 4145, 4147, 4148, 4149, 4151, 4152
    ] := by nativeDecideFin!
