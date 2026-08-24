import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 27 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `17` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `17` equations. -/
theorem rigid3_refutes_26 :
    FamilyRefutes Magma.rigid3 [
      3598, 3599, 3602, 3603, 3605, 3606, 3609, 3610, 3611, 3613, 3614, 3615, 3616, 3618, 3619,
      3622, 3623
    ] := by nativeDecideFin!
