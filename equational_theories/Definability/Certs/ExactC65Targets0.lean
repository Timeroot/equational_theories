import equational_theories.Definability.ExactAut5C65

/-!
# Structural certificate targets: `Magma.exactC65` (part 1 of 1)

Equations with no model among the `2592` magmas on `Fin 5` whose automorphism group is exactly the
order-`6` group of `Magma.permEC65`. `19` of them are worth listing, of which `19` appear here; each
is a valid *target* `L` of a `Magma.exactC65` certificate, and so is not structural from any of the
`50` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2592` magmas on `Fin 5` whose automorphism group is exactly the order-`6` group of
`Magma.permEC65` satisfies any of these `19` equations. -/
theorem exactC65_refutes_0 :
    FamilyRefutes Magma.exactC65 [
      127, 160, 179, 212, 315, 362, 1085, 1278, 1655, 1657, 1721, 1851, 1860, 2254, 3474, 3667,
      3668, 3687, 3868
    ] := by nativeDecideFin!
