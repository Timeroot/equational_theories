import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 33 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `17` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `17` equations. -/
theorem rigid3_refutes_32 :
    FamilyRefutes Magma.rigid3 [
      3801, 3802, 3805, 3806, 3808, 3809, 3812, 3813, 3814, 3816, 3817, 3818, 3819, 3821, 3822,
      3825, 3826
    ] := by nativeDecideFin!
