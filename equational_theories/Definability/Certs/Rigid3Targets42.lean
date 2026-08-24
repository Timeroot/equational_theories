import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 43 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `16` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `16` equations. -/
theorem rigid3_refutes_42 :
    FamilyRefutes Magma.rigid3 [
      4064, 4156, 4159, 4160, 4163, 4166, 4169, 4170, 4172, 4173, 4174, 4177, 4178, 4180, 4181,
      4184
    ] := by nativeDecideFin!
