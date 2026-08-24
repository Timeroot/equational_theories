import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 47 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `9` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `9` equations. -/
theorem rigid3_refutes_46 :
    FamilyRefutes Magma.rigid3 [
      4251, 4252, 4254, 4255, 4256, 4257, 4259, 4260, 4261
    ] := by nativeDecideFin!
