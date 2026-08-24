import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 4 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `31` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `31` equations. -/
theorem rigid3_refutes_3 :
    FamilyRefutes Magma.rigid3 [
      428, 463, 469, 476, 479, 483, 487, 491, 495, 503, 504, 506, 508, 510, 516, 520, 524, 532,
      537, 541, 545, 549, 554, 558, 566, 571, 579, 583, 588, 593, 598
    ] := by nativeDecideFin!
