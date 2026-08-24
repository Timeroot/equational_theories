import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 45 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `17` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `17` equations. -/
theorem rigid3_refutes_44 :
    FamilyRefutes Magma.rigid3 [
      4207, 4208, 4211, 4212, 4214, 4215, 4218, 4219, 4220, 4222, 4223, 4224, 4225, 4227, 4228,
      4231, 4232
    ] := by nativeDecideFin!
