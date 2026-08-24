import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 37 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `16` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `16` equations. -/
theorem rigid3_refutes_36 :
    FamilyRefutes Magma.rigid3 [
      3861, 3953, 3956, 3957, 3960, 3963, 3966, 3967, 3969, 3970, 3971, 3974, 3975, 3977, 3978,
      3981
    ] := by nativeDecideFin!
