import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 7 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_6 :
    FamilyRefutes Magma.reflective3 [
      1352, 1354, 1355, 1356, 1359, 1360, 1362, 1363, 1364, 1365, 1367, 1368, 1369, 1371, 1372,
      1373, 1375, 1376, 1377, 1379, 1380, 1381, 1382, 1384, 1385, 1386, 1388, 1389, 1390, 1392,
      1393, 1394, 1396, 1397, 1398, 1399, 1401, 1402, 1403, 1404, 1406, 1407, 1408, 1409, 1411,
      1412, 1413, 1414, 1416, 1417, 1418, 1419, 1421, 1422, 1423, 1424, 1425, 1480, 1483, 1485,
      1486, 1487, 1489, 1490, 1493, 1495, 1496, 1497, 1499, 1500, 1501, 1503, 1505, 1508, 1509,
      1511, 1512, 1513, 1514, 1516, 1517, 1520, 1522, 1524, 1526, 1527, 1529, 1530, 1532, 1533,
      1534, 1536, 1537, 1538, 1540, 1541, 1542, 1544, 1545, 1546
    ] := by decide!
