import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 2 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `39` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `39` equations. -/
theorem exactC45_refutes_1 :
    FamilyRefutes Magma.exactC45 [
      376, 379, 380, 382, 383, 386, 389, 390, 392, 393, 394, 396, 397, 398, 400, 401, 402, 404,
      405, 406, 408, 409, 410, 723, 765, 778, 841, 882, 883, 934, 968, 1043, 1096, 1119, 1133,
      1150, 1167, 1202, 1246
    ] := by nativeDecideFin!
