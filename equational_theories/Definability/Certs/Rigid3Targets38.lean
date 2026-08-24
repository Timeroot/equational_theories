import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 39 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `17` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `17` equations. -/
theorem rigid3_refutes_38 :
    FamilyRefutes Magma.rigid3 [
      4004, 4005, 4008, 4009, 4011, 4012, 4015, 4016, 4017, 4019, 4020, 4021, 4022, 4024, 4025,
      4028, 4029
    ] := by nativeDecideFin!
