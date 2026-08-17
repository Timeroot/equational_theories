import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.cyclic4` (part 2 of 4)

Equations in at most four variables with no model among the `256` magmas on `Fin 4` admitting the
cyclic shift `x ↦ x + 1` as an automorphism. Each of them is a valid *target* `L` of a
`Magma.cyclic4` certificate, and so is not definable from any of the five sources.

Only an implication-minimal subset of the family's equations is listed: a target stays a target
for every equation implying it, and a source stays a source for every equation it implies. The
`66` targets are implied by all `2306` of the targets in at most four variables, and the `5`
sources between them imply all `2041` of the sources, so these lists give exactly the certificates
the full ones would.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `256` magmas on `Fin 4` admitting the cyclic shift `x ↦ x + 1` as an automorphism
satisfies any of these `17` equations. -/
theorem cyclic4_refutes_1 :
    FamilyRefutes Magma.cyclic4 [
      870, 873, 883, 907, 917, 1076, 1086, 1110, 1113, 1276, 1279, 1286, 1289, 1313, 1480, 1483,
      1485
    ] := by decide!
