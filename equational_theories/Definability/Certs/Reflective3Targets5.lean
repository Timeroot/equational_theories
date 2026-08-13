import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 6 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_5 :
    FamilyRefutes Magma.reflective3 [
      1157, 1159, 1160, 1161, 1162, 1164, 1166, 1168, 1169, 1170, 1172, 1173, 1174, 1176, 1177,
      1178, 1179, 1182, 1183, 1185, 1186, 1187, 1189, 1190, 1191, 1193, 1194, 1195, 1196, 1198,
      1199, 1200, 1201, 1203, 1204, 1205, 1206, 1208, 1209, 1210, 1211, 1213, 1214, 1215, 1216,
      1218, 1219, 1220, 1221, 1222, 1277, 1279, 1280, 1282, 1283, 1284, 1286, 1287, 1290, 1292,
      1294, 1296, 1297, 1298, 1300, 1301, 1302, 1305, 1306, 1308, 1309, 1310, 1311, 1313, 1314,
      1317, 1319, 1321, 1323, 1324, 1326, 1327, 1329, 1330, 1331, 1333, 1334, 1335, 1337, 1338,
      1339, 1341, 1342, 1343, 1345, 1346, 1347, 1348, 1350, 1351
    ] := by decide!
