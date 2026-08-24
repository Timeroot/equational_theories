import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 40 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `14` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `14` equations. -/
theorem rigid3_refutes_39 :
    FamilyRefutes Magma.rigid3 [
      4030, 4032, 4033, 4034, 4036, 4037, 4038, 4039, 4041, 4042, 4043, 4044, 4046, 4047
    ] := by nativeDecideFin!
