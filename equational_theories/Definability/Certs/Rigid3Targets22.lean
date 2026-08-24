import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 23 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `11` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `11` equations. -/
theorem rigid3_refutes_22 :
    FamilyRefutes Magma.rigid3 [
      3435, 3437, 3438, 3439, 3440, 3442, 3443, 3444, 3445, 3447, 3448
    ] := by nativeDecideFin!
