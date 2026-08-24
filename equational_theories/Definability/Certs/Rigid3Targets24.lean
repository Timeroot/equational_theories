import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 25 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `16` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `16` equations. -/
theorem rigid3_refutes_24 :
    FamilyRefutes Magma.rigid3 [
      3455, 3547, 3550, 3551, 3554, 3557, 3560, 3561, 3563, 3564, 3565, 3568, 3569, 3571, 3572,
      3575
    ] := by nativeDecideFin!
