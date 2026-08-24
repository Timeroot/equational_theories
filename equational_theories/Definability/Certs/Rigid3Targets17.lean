import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 18 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `38` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `38` equations. -/
theorem rigid3_refutes_17 :
    FamilyRefutes Magma.rigid3 [
      2492, 2499, 2609, 2650, 2653, 2656, 2663, 2666, 2670, 2677, 2685, 2737, 2741, 2856, 2860,
      2863, 2873, 2883, 2888, 2891, 3051, 3054, 3057, 3059, 3060, 3062, 3063, 3064, 3067, 3069,
      3070, 3072, 3073, 3074, 3076, 3077, 3080, 3082
    ] := by nativeDecideFin!
