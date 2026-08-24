import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 20 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `20` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `20` equations. -/
theorem rigid3_refutes_19 :
    FamilyRefutes Magma.rigid3 [
      3361, 3362, 3365, 3366, 3368, 3369, 3372, 3373, 3374, 3376, 3377, 3378, 3379, 3381, 3382,
      3383, 3386, 3387, 3389, 3390
    ] := by nativeDecideFin!
