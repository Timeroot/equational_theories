import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 28 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `14` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `14` equations. -/
theorem rigid3_refutes_27 :
    FamilyRefutes Magma.rigid3 [
      3624, 3626, 3627, 3628, 3630, 3631, 3632, 3633, 3635, 3636, 3637, 3638, 3640, 3641
    ] := by nativeDecideFin!
