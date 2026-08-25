import equational_theories.Definability.ExactAut6C2A4b6

/-!
# Structural certificate targets: `Magma.exactC2A4b6` (part 1 of 1)

Equations with no model among the `72` magmas on `Fin 6` whose automorphism group is exactly the
order-`24` group of `Magma.permEC2A4b6`. `2` of them are worth listing, of which `2` appear here;
each is a valid *target* `L` of a `Magma.exactC2A4b6` certificate, and so is not structural from any
of the `2` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `72` magmas on `Fin 6` whose automorphism group is exactly the order-`24` group of
`Magma.permEC2A4b6` satisfies any of these `2` equations. -/
theorem exactC2A4b6_refutes_0 :
    FamilyRefutes Magma.exactC2A4b6 [
      3331, 3534
    ] := by nativeDecideFin!
