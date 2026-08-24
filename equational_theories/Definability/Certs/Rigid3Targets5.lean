import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 6 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `24` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `24` equations. -/
theorem rigid3_refutes_5 :
    FamilyRefutes Magma.rigid3 [
      1141, 1146, 1150, 1154, 1158, 1163, 1167, 1171, 1175, 1180, 1188, 1192, 1197, 1202, 1207,
      1212, 1217, 1275, 1281, 1285, 1288, 1291, 1295, 1299
    ] := by nativeDecideFin!
