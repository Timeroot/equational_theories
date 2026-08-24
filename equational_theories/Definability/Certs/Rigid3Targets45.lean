import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 46 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `14` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `14` equations. -/
theorem rigid3_refutes_45 :
    FamilyRefutes Magma.rigid3 [
      4233, 4235, 4236, 4237, 4239, 4240, 4241, 4242, 4244, 4245, 4246, 4247, 4249, 4250
    ] := by nativeDecideFin!
