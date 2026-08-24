import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 9 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `26` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `26` equations. -/
theorem rigid3_refutes_8 :
    FamilyRefutes Magma.rigid3 [
      1472, 1473, 1474, 1475, 1476, 1477, 1491, 1506, 1518, 1525, 1560, 1577, 1586, 1590, 1636,
      1639, 1642, 1643, 1646, 1648, 1649, 1651, 1652, 1653, 1656, 1659
    ] := by nativeDecideFin!
