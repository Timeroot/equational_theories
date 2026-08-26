import equational_theories.Definability.ExactEnd4F

/-!
# Term-structural certificate sources: `Magma.end4F`

For each of the following magmas, drawn from the `9` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`7` monoid of `Magma.endE4F`, the equations it satisfies that no earlier listed
magma does. Together they are the `163` equations that are worth using as the *source* `L'` of a
`Magma.end4F` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `6` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `66` equations satisfied by `Magma.end4F 0`, and by no earlier member of the cover. -/
theorem end4F_satisfies_0 :
    Satisfies (Magma.end4F 0) [
      317, 325, 371, 3263, 3270, 3280, 3283, 3284, 3287, 3296, 3299, 3468, 3477, 3483, 3487,
      3488, 3490, 3493, 3505, 3666, 3679, 3698, 3701, 3866, 3884, 3889, 3893, 3894, 3896, 3898,
      3902, 3910, 4072, 4085, 4087, 4101, 4104, 4105, 4107, 4113, 4277, 4288, 4294, 4297, 4299,
      4304, 4308, 4312, 4392, 4397, 4401, 4410, 4412, 4417, 4423, 4424, 4425, 4426, 4429, 4475,
      4486, 4495, 4503, 4594, 4601, 4611
    ] := by decide!

/-- `59` equations satisfied by `Magma.end4F 1`, and by no earlier member of the cover. -/
theorem end4F_satisfies_1 :
    Satisfies (Magma.end4F 1) [
      319, 372, 385, 3275, 3469, 3479, 3491, 3492, 3504, 3506, 3671, 3680, 3696, 3708, 3869,
      3875, 3882, 3885, 3901, 3904, 3912, 4075, 4078, 4082, 4088, 4108, 4110, 4111, 4115, 4279,
      4318, 4324, 4327, 4331, 4336, 4337, 4393, 4434, 4440, 4447, 4452, 4457, 4460, 4462, 4463,
      4467, 4477, 4487, 4489, 4494, 4504, 4595, 4603, 4612, 4614, 4619, 4627, 4661, 4670
    ] := by decide!

/-- `17` equations satisfied by `Magma.end4F 8`, and by no earlier member of the cover. -/
theorem end4F_satisfies_2 :
    Satisfies (Magma.end4F 8) [
      455, 504, 508, 622, 643, 658, 676, 731, 910, 914, 981, 1523, 1929, 2132, 2949, 2964, 3011
    ] := by decide!

/-- `8` equations satisfied by `Magma.end4F 3`, and by no earlier member of the cover. -/
theorem end4F_satisfies_3 :
    Satisfies (Magma.end4F 3) [
      104, 1025, 1060, 1228, 1238, 1240, 1258, 1263
    ] := by decide!

/-- `7` equations satisfied by `Magma.end4F 7`, and by no earlier member of the cover. -/
theorem end4F_satisfies_4 :
    Satisfies (Magma.end4F 7) [
      647, 1726, 2741, 2853, 2880, 3147, 3214
    ] := by decide!

/-- `6` equations satisfied by `Magma.end4F 5`, and by no earlier member of the cover. -/
theorem end4F_satisfies_5 :
    Satisfies (Magma.end4F 5) [
      205, 2240, 2249, 2296, 2351, 2554
    ] := by decide!
