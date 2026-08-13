import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 4 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_3 :
    FamilyRefutes Magma.reflective3 [
      762, 763, 764, 766, 767, 768, 770, 771, 772, 773, 775, 776, 777, 779, 780, 781, 783, 784,
      785, 787, 788, 789, 790, 792, 793, 794, 795, 797, 798, 799, 800, 802, 803, 804, 805, 807,
      808, 809, 810, 812, 813, 814, 815, 816, 871, 874, 876, 877, 878, 881, 883, 884, 886, 887,
      888, 890, 891, 892, 894, 895, 896, 898, 899, 900, 902, 903, 904, 905, 908, 911, 913, 915,
      918, 920, 921, 923, 924, 925, 927, 929, 931, 932, 933, 935, 936, 937, 939, 940, 941, 942,
      944, 945, 946, 948, 949, 950, 953, 954, 956, 957
    ] := by decide!
