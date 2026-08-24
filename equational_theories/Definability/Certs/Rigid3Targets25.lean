import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 26 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `16` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `16` equations. -/
theorem rigid3_refutes_25 :
    FamilyRefutes Magma.rigid3 [
      3576, 3577, 3579, 3580, 3581, 3582, 3584, 3585, 3586, 3589, 3590, 3592, 3593, 3594, 3596,
      3597
    ] := by nativeDecideFin!
