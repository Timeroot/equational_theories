import equational_theories.Definability.ExactAut7PSL7

/-!
# Structural certificate sources: `Magma.exactPSL7`

For each of the following magmas, drawn from the `1` magmas on `Fin 7` whose automorphism group is
exactly the order-`168` group of `Magma.permEPSL7`, the equations it satisfies that no earlier
listed magma does. Together they are the `158` equations that are worth using as the *source* `L'`
of a `Magma.exactPSL7` certificate -- the rest have such a model too, but the resulting facts are
already implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut7`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrPSL7`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `158` equations satisfied by `Magma.exactPSL7 0`, and by no earlier member of the cover. -/
theorem exactPSL7_satisfies_0 :
    Satisfies (Magma.exactPSL7 0) [
      14, 29, 43, 66, 115, 170, 177, 219, 281, 313, 332, 365, 387, 464, 477, 489, 492, 511, 522,
      572, 680, 684, 692, 711, 714, 725, 746, 759, 873, 880, 907, 1073, 1120, 1152, 1155, 1165,
      1171, 1181, 1276, 1289, 1293, 1304, 1320, 1340, 1358, 1374, 1467, 1470, 1479, 1492, 1504,
      1507, 1519, 1558, 1561, 1670, 1695, 1699, 1707, 1719, 1793, 1876, 1888, 1932, 1943, 1977,
      1983, 2088, 2128, 2135, 2167, 2170, 2180, 2186, 2196, 2199, 2271, 2279, 2291, 2335, 2338,
      2349, 2373, 2399, 2482, 2494, 2507, 2519, 2522, 2573, 2576, 2700, 2707, 2734, 2913, 2917,
      2925, 2944, 2947, 2958, 2979, 2992, 3103, 3116, 3120, 3131, 3150, 3195, 3211, 3272, 3331,
      3355, 3364, 3370, 3417, 3472, 3534, 3545, 3553, 3567, 3588, 3601, 3678, 3685, 3751, 3758,
      3878, 3964, 3994, 3997, 4007, 4013, 4026, 4091, 4154, 4162, 4167, 4182, 4200, 4216, 4273,
      4305, 4332, 4343, 4386, 4405, 4413, 4421, 4446, 4450, 4458, 4482, 4531, 4588, 4608, 4640,
      4647, 4677
    ] := by decide!
