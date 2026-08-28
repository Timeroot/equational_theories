import equational_theories.Definability.ExactEnd6K

/-!
# Term-structural certificate sources: `Magma.end6K`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`80` monoid of `Magma.endE6K`, the equations it satisfies that no earlier listed
magma does. Together they are the `133` equations that are worth using as the *source* `L'` of a
`Magma.end6K` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `73` equations satisfied by `Magma.end6K 0`, and by no earlier member of the cover. -/
theorem end6K_satisfies_0 :
    Satisfies (Magma.end6K 0) [
      16, 138, 166, 194, 364, 395, 500, 513, 528, 562, 575, 1025, 1055, 1085, 1096, 1112, 1122,
      1133, 1150, 1167, 1184, 1202, 1258, 1278, 1299, 1315, 1325, 1336, 1353, 1370, 1387, 1405,
      1634, 1668, 1681, 1701, 1721, 1742, 1763, 1780, 1797, 1816, 1847, 1875, 1884, 1897, 1912,
      1934, 1949, 1958, 1979, 2000, 2024, 2115, 2161, 2182, 2203, 2227, 3897, 3935, 3972, 3989,
      4006, 4040, 4070, 4100, 4138, 4175, 4192, 4209, 4645, 4666, 4689
    ] := by decide!

/-- `60` equations satisfied by `Magma.end6K 1`, and by no earlier member of the cover. -/
theorem end6K_satisfies_1 :
    Satisfies (Magma.end6K 1) [
      26, 152, 161, 212, 215, 308, 327, 1427, 1428, 1430, 1452, 1453, 1456, 1458, 1460, 1630,
      1631, 1633, 1656, 1658, 1659, 1660, 1661, 1662, 1663, 1833, 1837, 1839, 1851, 1852, 1862,
      1871, 1872, 1873, 1874, 2260, 2270, 2274, 2278, 2286, 2452, 2463, 2470, 2473, 2477, 2481,
      2485, 2489, 3091, 3317, 3320, 3321, 3322, 3324, 3460, 3520, 3523, 3524, 3525, 3527
    ] := by decide!
