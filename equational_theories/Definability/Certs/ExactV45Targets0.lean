import equational_theories.Definability.ExactAut5V45

/-!
# Structural certificate targets: `Magma.exactV45` (part 1 of 9)

Equations with no model among the `14442` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEV45`. `371` of them are worth listing, of which `121` appear here;
each is a valid *target* `L` of a `Magma.exactV45` certificate, and so is not structural from any of
the `281` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `14442` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEV45` satisfies any of these `121` equations. -/
theorem exactV45_refutes_0 :
    FamilyRefutes Magma.exactV45 [
      14, 29, 38, 39, 42, 45, 65, 106, 224, 261, 311, 322, 324, 328, 329, 330, 331, 332, 335,
      370, 381, 384, 387, 388, 391, 399, 403, 407, 433, 476, 489, 503, 655, 669, 676, 679, 690,
      692, 707, 713, 723, 731, 746, 834, 839, 841, 854, 861, 870, 872, 883, 887, 917, 947, 960,
      978, 981, 1043, 1082, 1086, 1101, 1246, 1247, 1260, 1261, 1276, 1285, 1312, 1316, 1323,
      1358, 1384, 1446, 1448, 1461, 1465, 1469, 1491, 1504, 1506, 1518, 1526, 1537, 1543, 1558,
      1560, 1586, 1697, 1705, 1707, 1729, 1740, 1868, 1869, 1898, 1902, 1977, 2045, 2046, 2054,
      2055, 2061, 2062, 2066, 2068, 2074, 2101, 2105, 2165, 2167, 2169, 2180, 2241, 2244, 2291,
      2304, 2306, 2319, 2322, 2331, 2333
    ] := by nativeDecideFin!
