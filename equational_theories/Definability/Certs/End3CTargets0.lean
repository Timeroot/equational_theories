import equational_theories.Definability.ExactEnd3C

/-!
# Term-structural certificate targets: `Magma.end3C`

Equations with no model among the `48` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`3` monoid of `Magma.endE3C`. `249` of them are worth listing, of which `249` appear here;
each is a valid *target* `L` of a `Magma.end3C` certificate, and so is not term-structural from any
of the `962` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `48` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`3` monoid of
`Magma.endE3C` satisfies any of these `249` equations. -/
theorem end3C_refutes_0 :
    FamilyRefutes Magma.end3C [
      3, 9, 28, 48, 49, 51, 52, 55, 58, 65, 72, 102, 103, 111, 228, 238, 242, 257, 258, 260, 261,
      263, 266, 270, 290, 332, 333, 335, 377, 384, 387, 412, 415, 418, 420, 421, 423, 424, 425,
      430, 437, 443, 616, 618, 619, 621, 625, 626, 627, 628, 629, 635, 642, 645, 649, 653, 657,
      661, 669, 679, 690, 713, 723, 822, 824, 826, 827, 828, 829, 830, 831, 832, 836, 838, 852,
      856, 860, 864, 879, 909, 916, 947, 960, 1024, 1027, 1029, 1030, 1032, 1033, 1034, 1042,
      1052, 1056, 1068, 1230, 1232, 1233, 1235, 1236, 1237, 1245, 1259, 1265, 1271, 1478, 1491,
      1506, 1518, 1525, 1560, 1586, 2036, 2044, 2045, 2054, 2055, 2061, 2062, 2310, 2314, 2337,
      2347, 2368, 2381, 2398, 2415, 2420, 2425, 2513, 2517, 2540, 2550, 2567, 2571, 2584, 2588,
      2601, 2618, 2623, 2646, 2649, 2650, 2653, 2655, 2656, 2663, 2665, 2666, 2675, 2679, 2683,
      2691, 2716, 2736, 2743, 2753, 2787, 2804, 2821, 2849, 2852, 2856, 2858, 2860, 2862, 2863,
      2868, 2873, 2875, 2878, 2882, 2883, 2886, 2890, 2894, 2919, 2956, 2973, 2990, 3024, 3102,
      3115, 3122, 3142, 3149, 3159, 3176, 3193, 3197, 3210, 3227, 3273, 3342, 3350, 3352, 3364,
      3370, 3417, 3476, 3495, 3545, 3546, 3553, 3555, 3558, 3566, 3567, 3573, 3588, 3607, 3669,
      3670, 3681, 3695, 3702, 3715, 3716, 3722, 3723, 3726, 3728, 3732, 3751, 3758, 3786, 3790,
      3803, 3874, 3899, 3927, 3930, 3951, 3961, 3964, 3973, 3979, 3994, 4013, 4026, 4102, 4162,
      4164, 4167, 4182, 4216, 4456, 4490, 4507, 4510
    ] := by nativeDecideFin!
