import equational_theories.Definability.ExactEnd3P

/-!
# Term-structural certificate sources: `Magma.end3P`

For each of the following magmas, drawn from the `12` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`5` monoid of `Magma.endE3P`, the equations it satisfies that no earlier listed
magma does. Together they are the `128` equations that are worth using as the *source* `L'` of a
`Magma.end3P` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `6` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `45` equations satisfied by `Magma.end3P 8`, and by no earlier member of the cover. -/
theorem end3P_satisfies_0 :
    Satisfies (Magma.end3P 8) [
      26, 630, 643, 647, 1442, 1451, 1455, 1459, 1645, 1654, 1658, 1662, 1873, 2038, 2041, 2064,
      2068, 2241, 2254, 2267, 2282, 2444, 2447, 2457, 2470, 2485, 2647, 2660, 2673, 2688, 2850,
      2853, 2876, 2880, 3053, 3056, 3066, 3079, 3083, 3091, 3094, 3917, 4383, 4469, 4477
    ] := by decide!

/-- `44` equations satisfied by `Magma.end3P 11`, and by no earlier member of the cover. -/
theorem end3P_satisfies_1 :
    Satisfies (Magma.end3P 11) [
      16, 466, 473, 500, 513, 528, 562, 575, 676, 703, 716, 731, 872, 906, 919, 981, 1075, 1082,
      1109, 1122, 1184, 1278, 1312, 1325, 1387, 1488, 1515, 1528, 1543, 1780, 1887, 1934, 1949,
      2043, 2090, 2137, 2152, 2902, 2949, 2964, 3549, 4388, 4409, 4424
    ] := by decide!

/-- `18` equations satisfied by `Magma.end3P 0`, and by no earlier member of the cover. -/
theorem end3P_satisfies_2 :
    Satisfies (Magma.end3P 0) [
      325, 327, 3317, 3320, 3324, 3520, 3523, 3524, 3527, 3666, 3863, 3866, 4381, 4382, 4397,
      4401, 4436, 4511
    ] := by decide!

/-- `18` equations satisfied by `Magma.end3P 2`, and by no earlier member of the cover. -/
theorem end3P_satisfies_3 :
    Satisfies (Magma.end3P 2) [
      385, 395, 3471, 3491, 3680, 3972, 3989, 4006, 4040, 4192, 4209, 4243, 4406, 4416, 4432,
      4452, 4483, 4494
    ] := by decide!

/-- `2` equations satisfied by `Magma.end3P 7`, and by no earlier member of the cover. -/
theorem end3P_satisfies_4 :
    Satisfies (Magma.end3P 7) [
      3667, 3868
    ] := by decide!

/-- `1` equations satisfied by `Magma.end3P 10`, and by no earlier member of the cover. -/
theorem end3P_satisfies_5 :
    Satisfies (Magma.end3P 10) [
      3474
    ] := by decide!
