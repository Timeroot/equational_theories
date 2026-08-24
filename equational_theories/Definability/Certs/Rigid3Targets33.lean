import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 34 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `14` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `14` equations. -/
theorem rigid3_refutes_33 :
    FamilyRefutes Magma.rigid3 [
      3827, 3829, 3830, 3831, 3833, 3834, 3835, 3836, 3838, 3839, 3840, 3841, 3843, 3844
    ] := by nativeDecideFin!
