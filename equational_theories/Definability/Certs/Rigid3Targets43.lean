import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 44 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `16` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `16` equations. -/
theorem rigid3_refutes_43 :
    FamilyRefutes Magma.rigid3 [
      4185, 4186, 4188, 4189, 4190, 4191, 4193, 4194, 4195, 4198, 4199, 4201, 4202, 4203, 4205,
      4206
    ] := by nativeDecideFin!
