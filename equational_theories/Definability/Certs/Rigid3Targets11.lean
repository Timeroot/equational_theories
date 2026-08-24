import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 12 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `22` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `22` equations. -/
theorem rigid3_refutes_11 :
    FamilyRefutes Magma.rigid3 [
      1849, 1852, 1854, 1856, 1859, 1862, 1864, 1866, 1870, 1872, 1874, 1876, 1877, 1878, 1879,
      1880, 1881, 1882, 1883, 1890, 1900, 1904
    ] := by nativeDecideFin!
