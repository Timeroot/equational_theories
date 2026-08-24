import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 17 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `24` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `24` equations. -/
theorem rigid3_refutes_16 :
    FamilyRefutes Magma.rigid3 [
      2455, 2458, 2460, 2461, 2463, 2464, 2465, 2467, 2468, 2471, 2473, 2474, 2475, 2477, 2478,
      2479, 2481, 2482, 2483, 2486, 2487, 2489, 2490, 2491
    ] := by nativeDecideFin!
