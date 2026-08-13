import equational_theories.Definability.Certificates

/-!
# Definability certificate targets: `Magma.reflective3` (part 8 of 16)

Equations with no model among the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism. There
are `1592` such equations in all, of which `100` are listed here; each of them is a valid *target*
`L` of a `Magma.reflective3` certificate, and so is not definable from any of the `3102` source
laws.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- None of the `81` magmas on `Fin 3` with `x ↦ -x` as an automorphism satisfies any of these
`100` equations. -/
theorem reflective3_refutes_7 :
    FamilyRefutes Magma.reflective3 [
      1548, 1549, 1550, 1551, 1553, 1554, 1555, 1557, 1559, 1562, 1563, 1565, 1566, 1567, 1568,
      1570, 1571, 1572, 1574, 1575, 1576, 1578, 1579, 1580, 1582, 1583, 1584, 1585, 1587, 1588,
      1589, 1591, 1592, 1593, 1595, 1596, 1597, 1599, 1600, 1601, 1602, 1604, 1605, 1606, 1607,
      1609, 1610, 1611, 1612, 1614, 1615, 1616, 1617, 1619, 1620, 1621, 1622, 1624, 1625, 1626,
      1627, 1628, 1682, 1683, 1686, 1688, 1689, 1690, 1693, 1696, 1698, 1700, 1702, 1703, 1704,
      1706, 1708, 1710, 1711, 1712, 1714, 1715, 1716, 1717, 1720, 1723, 1725, 1727, 1730, 1732,
      1733, 1735, 1736, 1737, 1739, 1741, 1743, 1744, 1745, 1747
    ] := by decide!
