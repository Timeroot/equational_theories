import equational_theories.Definability.ExactEnd5E

/-!
# Term-structural certificate sources: `Magma.end5E`

For each of the following magmas, drawn from the `6` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`25` monoid of `Magma.endE5E`, the equations it satisfies that no earlier listed
magma does. Together they are the `150` equations that are worth using as the *source* `L'` of a
`Magma.end5E` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `6` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `69` equations satisfied by `Magma.end5E 0`, and by no earlier member of the cover. -/
theorem end5E_satisfies_0 :
    Satisfies (Magma.end5E 0) [
      315, 317, 3263, 3270, 3280, 3283, 3284, 3287, 3296, 3299, 3468, 3473, 3477, 3483, 3484,
      3486, 3487, 3490, 3493, 3497, 3499, 3501, 3502, 3505, 3679, 3698, 3701, 3871, 3872, 3879,
      3889, 3892, 3893, 3896, 3907, 3908, 4277, 4288, 4294, 4297, 4299, 4304, 4308, 4312, 4386,
      4389, 4390, 4392, 4408, 4410, 4412, 4417, 4421, 4423, 4425, 4426, 4429, 4471, 4475, 4482,
      4484, 4486, 4491, 4495, 4497, 4498, 4499, 4500, 4503
    ] := by decide!

/-- `48` equations satisfied by `Magma.end5E 1`, and by no earlier member of the cover. -/
theorem end5E_satisfies_1 :
    Satisfies (Magma.end5E 1) [
      362, 372, 3469, 3479, 3506, 3671, 3696, 3708, 3869, 3875, 3882, 3885, 3901, 3903, 3904,
      3912, 4075, 4078, 4082, 4088, 4108, 4110, 4111, 4115, 4393, 4434, 4440, 4446, 4447, 4450,
      4457, 4460, 4461, 4462, 4463, 4467, 4479, 4487, 4489, 4504, 4595, 4603, 4612, 4614, 4619,
      4627, 4661, 4670
    ] := by decide!

/-- `17` equations satisfied by `Magma.end5E 5`, and by no earlier member of the cover. -/
theorem end5E_satisfies_2 :
    Satisfies (Magma.end5E 5) [
      455, 504, 508, 658, 676, 910, 914, 1082, 1312, 1519, 1523, 1925, 1929, 2128, 2132, 2459,
      3011
    ] := by decide!

/-- `10` equations satisfied by `Magma.end5E 4`, and by no earlier member of the cover. -/
theorem end5E_satisfies_3 :
    Satisfies (Magma.end5E 4) [
      1038, 1722, 1726, 2241, 2447, 2737, 2741, 2853, 3143, 3147
    ] := by decide!

/-- `3` equations satisfied by `Magma.end5E 2`, and by no earlier member of the cover. -/
theorem end5E_satisfies_4 :
    Satisfies (Magma.end5E 2) [
      1060, 1240, 1263
    ] := by decide!

/-- `3` equations satisfied by `Magma.end5E 3`, and by no earlier member of the cover. -/
theorem end5E_satisfies_5 :
    Satisfies (Magma.end5E 3) [
      2296, 2351, 2554
    ] := by decide!
