import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 2 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `27` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `27` equations. -/
theorem rigid3_refutes_1 :
    FamilyRefutes Magma.rigid3 [
      210, 212, 213, 215, 216, 217, 256, 258, 261, 273, 334, 337, 338, 340, 341, 342, 344, 345,
      346, 348, 349, 350, 352, 353, 354, 356, 357
    ] := by nativeDecideFin!
