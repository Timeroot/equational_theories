import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 1 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `44` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `44` equations. -/
theorem rigid3_refutes_0 :
    FamilyRefutes Magma.rigid3 [
      13, 19, 24, 27, 41, 44, 46, 53, 62, 65, 72, 114, 117, 120, 124, 127, 130, 134, 138, 142,
      146, 154, 155, 157, 158, 160, 161, 162, 163, 164, 165, 169, 172, 176, 179, 182, 186, 190,
      194, 198, 204, 206, 207, 209
    ] := by nativeDecideFin!
