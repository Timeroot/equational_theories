import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 21 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `16` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `16` equations. -/
theorem rigid3_refutes_20 :
    FamilyRefutes Magma.rigid3 [
      3391, 3393, 3394, 3395, 3396, 3399, 3400, 3402, 3403, 3406, 3407, 3408, 3410, 3411, 3412,
      3413
    ] := by nativeDecideFin!
