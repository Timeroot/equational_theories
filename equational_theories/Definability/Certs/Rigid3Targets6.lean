import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 7 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `25` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `25` equations. -/
theorem rigid3_refutes_6 :
    FamilyRefutes Magma.rigid3 [
      1303, 1307, 1315, 1318, 1322, 1328, 1332, 1336, 1340, 1344, 1349, 1353, 1357, 1361, 1366,
      1370, 1374, 1378, 1383, 1391, 1395, 1400, 1405, 1410, 1415
    ] := by nativeDecideFin!
