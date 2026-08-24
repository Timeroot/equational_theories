import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 19 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `23` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `23` equations. -/
theorem rigid3_refutes_18 :
    FamilyRefutes Magma.rigid3 [
      3084, 3086, 3087, 3088, 3090, 3092, 3095, 3096, 3098, 3099, 3100, 3101, 3108, 3143, 3147,
      3344, 3347, 3348, 3351, 3354, 3357, 3358, 3360
    ] := by nativeDecideFin!
