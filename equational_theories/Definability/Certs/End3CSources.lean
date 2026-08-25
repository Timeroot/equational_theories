import equational_theories.Definability.ExactEnd3C

/-!
# Term-structural certificate sources: `Magma.end3C`

For each of the following magmas, drawn from the `48` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`3` monoid of `Magma.endE3C`, the equations it satisfies that no earlier listed
magma does. Together they are the `962` equations that are worth using as the *source* `L'` of a
`Magma.end3C` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `17` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `419` equations satisfied by `Magma.end3C 14`, and by no earlier member of the cover. -/
theorem end3C_satisfies_0 :
    Satisfies (Magma.end3C 14) [
      24, 25, 26, 27, 38, 42, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163,
      164, 165, 204, 205, 206, 207, 209, 210, 212, 213, 214, 215, 216, 217, 322, 324, 325, 326,
      327, 328, 329, 330, 331, 1427, 1428, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438,
      1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453,
      1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468,
      1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1630, 1631, 1632, 1633, 1634, 1635,
      1636, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651,
      1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666,
      1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1833,
      1834, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849,
      1850, 1851, 1852, 1853, 1854, 1855, 1856, 1858, 1859, 1860, 1862, 1863, 1864, 1866, 1867,
      1868, 1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882,
      1883, 2239, 2240, 2241, 2242, 2244, 2245, 2247, 2248, 2249, 2250, 2251, 2252, 2254, 2255,
      2257, 2258, 2259, 2260, 2261, 2262, 2264, 2265, 2267, 2268, 2269, 2270, 2271, 2272, 2274,
      2275, 2276, 2278, 2279, 2280, 2282, 2283, 2284, 2285, 2286, 2287, 2288, 2289, 2442, 2443,
      2444, 2445, 2447, 2448, 2450, 2451, 2452, 2453, 2454, 2455, 2457, 2458, 2459, 2460, 2461,
      2462, 2463, 2464, 2465, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2477, 2478,
      2479, 2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 3051,
      3052, 3053, 3054, 3055, 3056, 3057, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067,
      3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083,
      3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098,
      3099, 3100, 3101, 3305, 3307, 3309, 3310, 3311, 3312, 3313, 3314, 3317, 3318, 3320, 3321,
      3322, 3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337,
      3338, 3339, 3340, 3341, 3508, 3510, 3513, 3514, 3515, 3516, 3517, 3520, 3521, 3523, 3524,
      3526, 3527, 3528, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3538, 3539, 3540, 3541, 3542,
      3543, 3544, 4077, 4079, 4117, 4119, 4121, 4122, 4123, 4124, 4125, 4126, 4129, 4130, 4132,
      4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4145, 4146, 4147,
      4148, 4149, 4150, 4151, 4152, 4153
    ] := by decide!

/-- `371` equations satisfied by `Magma.end3C 34`, and by no earlier member of the cover. -/
theorem end3C_satisfies_1 :
    Satisfies (Magma.end3C 34) [
      10, 13, 16, 19, 39, 45, 104, 110, 114, 117, 120, 124, 127, 130, 134, 138, 142, 146, 166,
      169, 172, 176, 179, 182, 186, 190, 194, 198, 375, 381, 385, 388, 391, 395, 399, 403, 407,
      413, 416, 419, 422, 426, 432, 439, 442, 446, 450, 454, 458, 463, 466, 469, 473, 476, 479,
      483, 487, 491, 495, 500, 503, 506, 510, 513, 516, 520, 524, 528, 532, 537, 541, 545, 549,
      554, 558, 562, 566, 571, 575, 579, 583, 588, 593, 598, 603, 608, 1035, 1038, 1041, 1048,
      1051, 1055, 1059, 1063, 1067, 1072, 1075, 1078, 1082, 1085, 1088, 1092, 1096, 1100, 1104,
      1109, 1112, 1115, 1119, 1122, 1125, 1129, 1133, 1137, 1141, 1146, 1150, 1154, 1158, 1163,
      1167, 1171, 1175, 1180, 1184, 1188, 1192, 1197, 1202, 1207, 1212, 1217, 1238, 1244, 1258,
      1266, 1270, 1275, 1278, 1281, 1285, 1288, 1291, 1295, 1299, 1303, 1307, 1312, 1315, 1318,
      1322, 1325, 1328, 1332, 1336, 1340, 1344, 1349, 1353, 1357, 1361, 1366, 1370, 1374, 1378,
      1383, 1387, 1391, 1395, 1400, 1405, 1410, 1415, 1420, 1681, 1684, 1687, 1691, 1694, 1697,
      1701, 1705, 1709, 1713, 1721, 1724, 1728, 1734, 1738, 1742, 1750, 1755, 1759, 1763, 1767,
      1772, 1776, 1780, 1784, 1789, 1793, 1797, 1801, 1806, 1811, 1816, 1821, 1826, 1884, 1887,
      1890, 1894, 1897, 1900, 1904, 1908, 1912, 1916, 1921, 1924, 1927, 1931, 1934, 1937, 1941,
      1945, 1949, 1953, 1958, 1962, 1966, 1970, 1975, 1979, 1983, 1987, 1992, 1996, 2000, 2004,
      2009, 2014, 2019, 2024, 2029, 2037, 2040, 2043, 2046, 2050, 2053, 2056, 2060, 2063, 2066,
      2070, 2074, 2078, 2082, 2087, 2090, 2093, 2097, 2100, 2103, 2107, 2111, 2115, 2119, 2127,
      2130, 2134, 2137, 2140, 2144, 2148, 2152, 2156, 2161, 2165, 2169, 2173, 2178, 2182, 2186,
      2190, 2195, 2199, 2203, 2207, 2212, 2217, 2222, 2227, 2232, 3292, 3300, 3343, 3349, 3356,
      3359, 3363, 3367, 3371, 3375, 3380, 3384, 3388, 3392, 3397, 3401, 3405, 3409, 3414, 3418,
      3422, 3426, 3431, 3436, 3441, 3446, 3451, 3918, 3921, 3935, 3939, 3947, 3952, 3958, 3965,
      3968, 3972, 3976, 3980, 3984, 3989, 3993, 4001, 4006, 4010, 4014, 4018, 4027, 4031, 4035,
      4040, 4045, 4050, 4055, 4060, 4161, 4168, 4171, 4175, 4179, 4183, 4187, 4196, 4204, 4209,
      4213, 4217, 4221, 4230, 4234, 4238, 4243, 4248, 4253, 4258, 4263
    ] := by decide!

/-- `46` equations satisfied by `Magma.end3C 25`, and by no earlier member of the cover. -/
theorem end3C_satisfies_2 :
    Satisfies (Magma.end3C 25) [
      47, 50, 53, 63, 75, 1073, 1086, 1090, 1101, 1113, 1117, 1155, 1692, 1722, 1726, 1761, 1898,
      1902, 1910, 1922, 2504, 2534, 2538, 2558, 2573, 2647, 2670, 2697, 2710, 2714, 2725, 2737,
      2741, 2779, 3113, 3143, 3147, 3182, 3214, 3548, 3601, 3617, 3770, 3794, 4157, 4210
    ] := by decide!

/-- `42` equations satisfied by `Magma.end3C 38`, and by no earlier member of the cover. -/
theorem end3C_satisfies_3 :
    Satisfies (Magma.end3C 38) [
      255, 264, 271, 273, 280, 455, 474, 504, 508, 543, 870, 882, 906, 910, 914, 917, 928, 952,
      978, 1053, 1083, 1152, 1685, 1729, 1740, 1774, 1895, 1925, 1929, 1964, 2494, 2541, 2552,
      2576, 2602, 3345, 3398, 3737, 3810, 3932, 3954, 4007
    ] := by decide!

/-- `18` equations satisfied by `Magma.end3C 21`, and by no earlier member of the cover. -/
theorem end3C_satisfies_4 :
    Satisfies (Magma.end3C 21) [
      56, 66, 73, 118, 125, 170, 177, 222, 229, 274, 281, 283, 4364, 4512, 4515, 4525, 4541, 4679
    ] := by decide!

/-- `13` equations satisfied by `Magma.end3C 19`, and by no earlier member of the cover. -/
theorem end3C_satisfies_5 :
    Satisfies (Magma.end3C 19) [
      617, 647, 1267, 2051, 2064, 2068, 2660, 2673, 2688, 2850, 2853, 2876, 2880
    ] := by decide!

/-- `13` equations satisfied by `Magma.end3C 20`, and by no earlier member of the cover. -/
theorem end3C_satisfies_6 :
    Satisfies (Magma.end3C 20) [
      676, 703, 716, 731, 872, 919, 981, 1481, 1528, 1543, 2402, 2936, 2964
    ] := by decide!

/-- `6` equations satisfied by `Magma.end3C 2`, and by no earlier member of the cover. -/
theorem end3C_satisfies_7 :
    Satisfies (Magma.end3C 2) [
      4399, 4403, 4413, 4415, 4420, 4430
    ] := by decide!

/-- `6` equations satisfied by `Magma.end3C 24`, and by no earlier member of the cover. -/
theorem end3C_satisfies_8 :
    Satisfies (Magma.end3C 24) [
      2592, 2808, 2909, 2998, 3112, 3201
    ] := by decide!

/-- `6` equations satisfied by `Magma.end3C 36`, and by no earlier member of the cover. -/
theorem end3C_satisfies_9 :
    Satisfies (Magma.end3C 36) [
      417, 452, 620, 655, 861, 1061
    ] := by decide!

/-- `5` equations satisfied by `Magma.end3C 6`, and by no earlier member of the cover. -/
theorem end3C_satisfies_10 :
    Satisfies (Magma.end3C 6) [
      1021, 1050, 1240, 1243, 1263
    ] := by decide!

/-- `5` equations satisfied by `Magma.end3C 16`, and by no earlier member of the cover. -/
theorem end3C_satisfies_11 :
    Satisfies (Magma.end3C 16) [
      2296, 2351, 2372, 2493, 2609
    ] := by decide!

/-- `4` equations satisfied by `Magma.end3C 45`, and by no earlier member of the cover. -/
theorem end3C_satisfies_12 :
    Satisfies (Magma.end3C 45) [
      1479, 1482, 2088, 2125
    ] := by decide!

/-- `3` equations satisfied by `Magma.end3C 10`, and by no earlier member of the cover. -/
theorem end3C_satisfies_13 :
    Satisfies (Magma.end3C 10) [
      615, 623, 624
    ] := by decide!

/-- `3` equations satisfied by `Magma.end3C 32`, and by no earlier member of the cover. -/
theorem end3C_satisfies_14 :
    Satisfies (Magma.end3C 32) [
      2899, 2946, 3007
    ] := by decide!

/-- `1` equations satisfied by `Magma.end3C 5`, and by no earlier member of the cover. -/
theorem end3C_satisfies_15 :
    Satisfies (Magma.end3C 5) [
      1060
    ] := by decide!

/-- `1` equations satisfied by `Magma.end3C 15`, and by no earlier member of the cover. -/
theorem end3C_satisfies_16 :
    Satisfies (Magma.end3C 15) [
      2554
    ] := by decide!
