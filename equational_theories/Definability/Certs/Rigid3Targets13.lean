import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 14 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `31` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `31` equations. -/
theorem rigid3_refutes_13 :
    FamilyRefutes Magma.rigid3 [
      2029, 2044, 2045, 2046, 2054, 2055, 2056, 2061, 2062, 2066, 2074, 2076, 2078, 2079, 2082,
      2093, 2100, 2103, 2107, 2111, 2115, 2119, 2130, 2140, 2144, 2148, 2156, 2173, 2178, 2182,
      2186
    ] := by nativeDecideFin!
