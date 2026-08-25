import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 32 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `16` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `16` equations. -/
theorem exactC45_refutes_31 :
    FamilyRefutes Magma.exactC45 [
      4021, 4022, 4024, 4025, 4028, 4029, 4030, 4032, 4033, 4034, 4036, 4037, 4038, 4039, 4041,
      4042
    ] := by nativeDecideFin!
