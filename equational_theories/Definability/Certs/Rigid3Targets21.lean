import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 22 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `15` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `15` equations. -/
theorem rigid3_refutes_21 :
    FamilyRefutes Magma.rigid3 [
      3415, 3416, 3419, 3420, 3421, 3423, 3424, 3425, 3427, 3428, 3429, 3430, 3432, 3433, 3434
    ] := by nativeDecideFin!
