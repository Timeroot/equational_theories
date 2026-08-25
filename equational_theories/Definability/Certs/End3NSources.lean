import equational_theories.Definability.ExactEnd3N

/-!
# Term-structural certificate sources: `Magma.end3N`

For each of the following magmas, drawn from the `2` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`8` monoid of `Magma.endE3N`, the equations it satisfies that no earlier listed
magma does. Together they are the `247` equations that are worth using as the *source* `L'` of a
`Magma.end3N` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `128` equations satisfied by `Magma.end3N 0`, and by no earlier member of the cover. -/
theorem end3N_satisfies_0 :
    Satisfies (Magma.end3N 0) [
      9, 48, 49, 50, 51, 100, 101, 103, 325, 327, 377, 412, 413, 414, 415, 416, 418, 420, 421,
      422, 423, 424, 425, 615, 616, 618, 619, 621, 622, 623, 624, 625, 626, 627, 628, 818, 819,
      820, 821, 822, 823, 824, 827, 828, 829, 830, 831, 1021, 1022, 1024, 1025, 1026, 1027, 1028,
      1030, 1031, 1032, 1033, 1034, 1224, 1225, 1227, 1228, 1229, 1230, 1231, 1233, 1234, 1235,
      1236, 1237, 1427, 1428, 1429, 1430, 1630, 1631, 1633, 1833, 1837, 1839, 2036, 2240, 2243,
      2246, 2249, 2443, 2446, 2452, 2646, 2852, 3316, 3317, 3321, 3322, 3324, 3458, 3460, 3518,
      3520, 3521, 3523, 3524, 3525, 3526, 3527, 3714, 3716, 3723, 3724, 3726, 3924, 3927, 3930,
      3931, 4120, 4127, 4128, 4314, 4315, 4339, 4357, 4436, 4507, 4510, 4511, 4629, 4673
    ] := by decide!

/-- `119` equations satisfied by `Magma.end3N 1`, and by no earlier member of the cover. -/
theorem end3N_satisfies_1 :
    Satisfies (Magma.end3N 1) [
      28, 208, 238, 260, 270, 280, 290, 333, 385, 395, 832, 1035, 1055, 1238, 1248, 1258, 1478,
      1634, 1681, 1701, 1847, 1884, 1958, 2050, 2087, 2124, 2161, 2253, 2263, 2273, 2290, 2300,
      2310, 2347, 2364, 2381, 2398, 2415, 2456, 2466, 2476, 2493, 2503, 2513, 2550, 2567, 2584,
      2601, 2618, 2649, 2659, 2679, 2696, 2706, 2716, 2733, 2753, 2770, 2787, 2804, 2821, 2862,
      2872, 2882, 2899, 2919, 2946, 2956, 2973, 2990, 3007, 3024, 3055, 3065, 3085, 3102, 3122,
      3139, 3149, 3159, 3176, 3193, 3210, 3227, 3346, 3353, 3529, 3546, 3556, 3566, 3749, 3752,
      3786, 3790, 3803, 3867, 3897, 3935, 3952, 3962, 3972, 3989, 4006, 4023, 4040, 4138, 4175,
      4209, 4226, 4243, 4291, 4362, 4406, 4416, 4456, 4490, 4615, 4645, 4689
    ] := by decide!
