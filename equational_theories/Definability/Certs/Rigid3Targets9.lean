import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 10 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `22` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `22` equations. -/
theorem rigid3_refutes_9 :
    FamilyRefutes Magma.rigid3 [
      1661, 1663, 1665, 1666, 1667, 1669, 1670, 1671, 1673, 1674, 1675, 1676, 1677, 1678, 1679,
      1680, 1687, 1709, 1713, 1722, 1726, 1734
    ] := by nativeDecideFin!
