import equational_theories.Definability.ExactAut6A46

/-!
# Structural certificate sources: `Magma.exactA46`

For each of the following magmas, drawn from the `64` magmas on `Fin 6` whose automorphism group is
exactly the order-`12` group of `Magma.permEA46`, the equations it satisfies that no earlier listed
magma does. Together they are the `201` equations that are worth using as the *source* `L'` of a
`Magma.exactA46` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrA46`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `103` equations satisfied by `Magma.exactA46 0`, and by no earlier member of the cover. -/
theorem exactA46_satisfies_0 :
    Satisfies (Magma.exactA46 0) [
      9, 48, 49, 50, 51, 100, 102, 152, 205, 308, 378, 412, 413, 414, 415, 416, 417, 418, 419,
      420, 421, 422, 423, 424, 425, 429, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625,
      626, 627, 628, 818, 819, 820, 821, 823, 825, 826, 829, 1021, 1022, 1024, 1026, 1029, 1032,
      1039, 1224, 1226, 1232, 1426, 1427, 1428, 1429, 1430, 1630, 1632, 1833, 1837, 1838, 1839,
      2036, 2051, 2238, 2240, 2243, 2246, 2249, 2443, 2449, 2646, 2852, 3254, 3255, 3256, 3257,
      3318, 3320, 3457, 3459, 3511, 3519, 3660, 3725, 3864, 3918, 3921, 3928, 4121, 4131, 4268,
      4282, 4395, 4473, 4599
    ] := by decide!

/-- `98` equations satisfied by `Magma.exactA46 5`, and by no earlier member of the cover. -/
theorem exactA46_satisfies_1 :
    Satisfies (Magma.exactA46 5) [
      28, 104, 166, 218, 228, 260, 270, 280, 290, 323, 364, 832, 1035, 1045, 1228, 1238, 1248,
      1258, 1478, 1481, 1634, 1681, 1691, 1701, 1884, 1921, 2050, 2087, 2124, 2161, 2290, 2327,
      2337, 2456, 2493, 2503, 2533, 2540, 2567, 2584, 2659, 2696, 2706, 2733, 2743, 2770, 2787,
      2862, 2872, 2882, 2899, 2909, 2919, 2936, 2946, 2956, 2973, 2990, 3007, 3024, 3055, 3065,
      3068, 3075, 3085, 3102, 3112, 3122, 3139, 3149, 3159, 3176, 3193, 3210, 3227, 3306, 3309,
      3461, 3509, 3512, 3533, 3674, 3712, 3877, 3887, 3925, 3955, 4070, 4080, 4090, 4100, 4155,
      4192, 4284, 4385, 4396, 4587, 4666
    ] := by decide!
