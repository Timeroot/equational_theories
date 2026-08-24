import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate targets: `Magma.rigid3` (part 5 of 49)

Equations with no rigid model on `Fin 3`. Each is a valid *target* `L` of a `Magma.rigid3`
certificate, and so is not structural from any of the `1776` equations that do have one, not even
over finite carriers. `38` of them are listed here.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `19422` rigid magmas on `Fin 3` satisfies any of these `38` equations. -/
theorem rigid3_refutes_4 :
    FamilyRefutes Magma.rigid3 [
      603, 608, 666, 669, 679, 690, 706, 713, 723, 765, 778, 879, 882, 909, 910, 914, 916, 934,
      947, 960, 968, 1037, 1050, 1072, 1078, 1085, 1088, 1092, 1096, 1100, 1104, 1112, 1115,
      1119, 1125, 1129, 1133, 1137
    ] := by nativeDecideFin!
