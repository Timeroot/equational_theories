import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 15 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `25` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `25` equations. -/
theorem rigid3_refutes_14 :
    FamilyRefutes Magma.rigid3 [
      2190, 2195, 2199, 2203, 2207, 2212, 2217, 2222, 2227, 2232, 2239, 2242, 2244, 2245, 2247,
      2248, 2250, 2251, 2252, 2255, 2257, 2258, 2260, 2261, 2262
    ] := by nativeDecideFin!
