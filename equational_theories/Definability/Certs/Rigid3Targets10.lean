import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 11 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `22` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `22` equations. -/
theorem rigid3_refutes_10 :
    FamilyRefutes Magma.rigid3 [
      1742, 1750, 1755, 1759, 1763, 1767, 1772, 1776, 1784, 1789, 1793, 1797, 1801, 1806, 1811,
      1816, 1821, 1826, 1836, 1842, 1844, 1846
    ] := by nativeDecideFin!
