import equational_theories.Definability.ExactEnd4E

/-!
# Term-structural certificate sources: `Magma.end4E`

For each of the following magmas, drawn from the `4` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`13` monoid of `Magma.endE4E`, the equations it satisfies that no earlier listed
magma does. Together they are the `242` equations that are worth using as the *source* `L'` of a
`Magma.end4E` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `125` equations satisfied by `Magma.end4E 2`, and by no earlier member of the cover. -/
theorem end4E_satisfies_0 :
    Satisfies (Magma.end4E 2) [
      28, 75, 104, 166, 208, 238, 260, 270, 290, 333, 364, 385, 395, 476, 503, 510, 619, 706,
      727, 832, 882, 964, 1025, 1055, 1228, 1238, 1258, 1454, 1478, 1594, 1634, 1681, 1691, 1701,
      1847, 1884, 1958, 2050, 2087, 2161, 2243, 2273, 2310, 2347, 2381, 2398, 2415, 2446, 2456,
      2476, 2513, 2550, 2567, 2584, 2601, 2618, 2649, 2679, 2716, 2753, 2787, 2804, 2821, 2852,
      2862, 2882, 2919, 2956, 2973, 2990, 3024, 3055, 3065, 3085, 3102, 3122, 3149, 3159, 3176,
      3193, 3210, 3227, 3281, 3346, 3353, 3461, 3512, 3533, 3546, 3556, 3566, 3790, 3803, 3867,
      3897, 3925, 3935, 3952, 3962, 3972, 3989, 4006, 4023, 4040, 4070, 4080, 4100, 4128, 4138,
      4155, 4175, 4192, 4209, 4243, 4362, 4385, 4445, 4456, 4490, 4587, 4606, 4615, 4645, 4666,
      4689
    ] := by decide!

/-- `117` equations satisfied by `Magma.end4E 0`, and by no earlier member of the cover. -/
theorem end4E_satisfies_1 :
    Satisfies (Magma.end4E 0) [
      9, 48, 49, 51, 152, 205, 264, 308, 325, 327, 377, 412, 413, 415, 416, 418, 420, 421, 422,
      423, 424, 425, 616, 618, 621, 625, 626, 627, 628, 822, 824, 827, 828, 829, 830, 831, 1022,
      1024, 1027, 1030, 1031, 1032, 1033, 1034, 1230, 1233, 1234, 1235, 1236, 1237, 1427, 1428,
      1430, 1630, 1631, 1633, 1833, 1837, 1838, 1839, 2036, 2063, 2065, 2240, 2249, 2452, 2646,
      2670, 2676, 2866, 2887, 3059, 3069, 3076, 3254, 3255, 3257, 3316, 3317, 3318, 3320, 3321,
      3322, 3324, 3458, 3460, 3518, 3519, 3520, 3521, 3523, 3524, 3525, 3526, 3527, 3716, 3723,
      3864, 3918, 3921, 3924, 3927, 3930, 4074, 4120, 4127, 4268, 4282, 4314, 4315, 4339, 4357,
      4395, 4472, 4507, 4510, 4673
    ] := by decide!
