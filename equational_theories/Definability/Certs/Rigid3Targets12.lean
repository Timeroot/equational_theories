import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 13 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `25` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `25` equations. -/
theorem rigid3_refutes_12 :
    FamilyRefutes Magma.rigid3 [
      1908, 1912, 1916, 1924, 1925, 1927, 1929, 1937, 1941, 1945, 1953, 1962, 1966, 1970, 1979,
      1983, 1987, 1992, 1996, 2000, 2004, 2009, 2014, 2019, 2024
    ] := by nativeDecideFin!
