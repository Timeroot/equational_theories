import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 3 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `19` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `19` equations. -/
theorem rigid3_refutes_2 :
    FamilyRefutes Magma.rigid3 [
      358, 386, 389, 390, 392, 393, 394, 396, 397, 398, 400, 401, 402, 404, 405, 406, 408, 409,
      410
    ] := by nativeDecideFin!
