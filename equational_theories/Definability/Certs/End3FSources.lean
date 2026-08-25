import equational_theories.Definability.ExactEnd3F

/-!
# Term-structural certificate sources: `Magma.end3F`

For each of the following magmas, drawn from the `1` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`9` monoid of `Magma.endE3F`, the equations it satisfies that no earlier listed
magma does. Together they are the `136` equations that are worth using as the *source* `L'` of a
`Magma.end3F` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `136` equations satisfied by `Magma.end3F 0`, and by no earlier member of the cover. -/
theorem end3F_satisfies_0 :
    Satisfies (Magma.end3F 0) [
      14, 29, 66, 115, 170, 177, 219, 281, 313, 365, 387, 464, 477, 489, 492, 511, 522, 572, 680,
      684, 692, 707, 711, 714, 725, 746, 759, 873, 880, 907, 1073, 1113, 1120, 1152, 1155, 1165,
      1171, 1181, 1276, 1289, 1293, 1304, 1316, 1320, 1340, 1358, 1374, 1467, 1470, 1479, 1492,
      1504, 1507, 1519, 1558, 1561, 1670, 1695, 1699, 1707, 1719, 1793, 1876, 1888, 1932, 1943,
      1977, 1983, 2088, 2128, 2135, 2167, 2170, 2180, 2186, 2196, 2199, 2271, 2279, 2291, 2331,
      2335, 2338, 2349, 2373, 2399, 2482, 2494, 2507, 2519, 2522, 2534, 2573, 2576, 2700, 2707,
      2734, 2913, 2917, 2925, 2940, 2944, 2947, 2958, 2979, 2992, 3103, 3116, 3120, 3131, 3150,
      3195, 3211, 3355, 3364, 3370, 3417, 3553, 3567, 3601, 3678, 3685, 3751, 3758, 4007, 4013,
      4026, 4154, 4162, 4182, 4216, 4305, 4413, 4421, 4450, 4640
    ] := by decide!
