import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 3 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_2 :
    FamilyRefutes Magma.reflective3 [
      564, 565, 567, 568, 569, 570, 573, 574, 576, 577, 578, 580, 581, 582, 584, 585, 586, 587,
      589, 590, 591, 592, 594, 595, 596, 597, 599, 600, 601, 602, 604, 605, 606, 607, 609, 610,
      611, 612, 613, 667, 668, 670, 671, 673, 674, 675, 677, 678, 681, 683, 685, 687, 688, 689,
      691, 693, 695, 696, 697, 699, 700, 701, 702, 704, 705, 708, 710, 712, 715, 717, 718, 720,
      721, 722, 724, 726, 728, 729, 730, 732, 733, 734, 736, 737, 738, 739, 741, 742, 743, 745,
      747, 749, 750, 751, 753, 754, 755, 756, 758, 760
    ] := by decide!
