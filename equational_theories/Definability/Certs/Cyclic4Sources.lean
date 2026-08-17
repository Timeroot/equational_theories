import equational_theories.Definability.Certificates

/-!
# Definability certificate sources: `Magma.cyclic4`

For each of five of the `256` magmas on `Fin 4` admitting the cyclic shift `x ↦ x + 1` as an
automorphism, an equation in at most four variables that it satisfies, and so may be used as the
*source* `L'` of a `Magma.cyclic4` certificate.

Only an implication-minimal subset of the family's equations is listed: a target stays a target
for every equation implying it, and a source stays a source for every equation it implies. The
`66` targets are implied by all `2306` of the targets in at most four variables, and the `5`
sources between them imply all `2041` of the sources, so these lists give exactly the certificates
the full ones would.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- The equation of the list satisfied by `Magma.cyclic4 1 0 1 3`. -/
theorem cyclic4_satisfies_71 :
    Satisfies (Magma.cyclic4 1 0 1 3) [
      1482
    ] := by decide!

/-- The equation of the list satisfied by `Magma.cyclic4 1 0 3 3`. -/
theorem cyclic4_satisfies_79 :
    Satisfies (Magma.cyclic4 1 0 3 3) [
      1479
    ] := by decide!

/-- The equation of the list satisfied by `Magma.cyclic4 1 1 3 0`. -/
theorem cyclic4_satisfies_92 :
    Satisfies (Magma.cyclic4 1 1 3 0) [
      4408
    ] := by decide!

/-- The equation of the list satisfied by `Magma.cyclic4 1 2 2 0`. -/
theorem cyclic4_satisfies_104 :
    Satisfies (Magma.cyclic4 1 2 2 0) [
      4290
    ] := by decide!

/-- The equation of the list satisfied by `Magma.cyclic4 1 3 0 2`. -/
theorem cyclic4_satisfies_114 :
    Satisfies (Magma.cyclic4 1 3 0 2) [
      670
    ] := by decide!
