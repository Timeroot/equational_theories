import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 16 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `25` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `25` equations. -/
theorem rigid3_refutes_15 :
    FamilyRefutes Magma.rigid3 [
      2264, 2265, 2268, 2270, 2271, 2272, 2274, 2275, 2276, 2278, 2279, 2280, 2283, 2284, 2286,
      2287, 2288, 2289, 2442, 2445, 2448, 2450, 2451, 2453, 2454
    ] := by nativeDecideFin!
