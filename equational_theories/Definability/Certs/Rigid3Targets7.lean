import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 8 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `27` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `27` equations. -/
theorem rigid3_refutes_7 :
    FamilyRefutes Magma.rigid3 [
      1420, 1433, 1436, 1438, 1439, 1440, 1443, 1447, 1449, 1450, 1452, 1453, 1456, 1457, 1458,
      1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471
    ] := by nativeDecideFin!
