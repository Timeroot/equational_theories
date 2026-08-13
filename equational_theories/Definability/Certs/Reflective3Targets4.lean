import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 5 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_4 :
    FamilyRefutes Magma.reflective3 [
      958, 959, 961, 962, 963, 965, 966, 967, 969, 970, 971, 973, 974, 975, 976, 979, 980, 982,
      983, 984, 986, 987, 988, 990, 991, 992, 993, 995, 996, 997, 998, 1000, 1001, 1002, 1003,
      1005, 1006, 1007, 1008, 1010, 1011, 1012, 1013, 1015, 1016, 1017, 1018, 1019, 1074, 1076,
      1077, 1079, 1080, 1081, 1084, 1087, 1089, 1091, 1093, 1094, 1095, 1097, 1098, 1099, 1102,
      1103, 1105, 1106, 1107, 1108, 1110, 1111, 1114, 1116, 1118, 1121, 1123, 1124, 1126, 1127,
      1128, 1130, 1131, 1132, 1134, 1135, 1136, 1138, 1139, 1140, 1142, 1143, 1144, 1145, 1147,
      1148, 1149, 1151, 1153, 1156
    ] := by decide!
