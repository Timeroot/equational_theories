import equational_theories.Definability.Srch_S8R66

/-!
# Structural certificate sources: `Magma.srch8R66`

For each of the `11` exhibited members of the class, the equations it satisfies that no earlier
listed member does. Together they are the `551` equations worth using as the *source* `L'` of a
`Magma.srch8R66` certificate.

This file is generated; see the module docstring of `Definability.Srch_S8R66_data`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- `453` equations satisfied by `Magma.srch8R66 vsrch8R660`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_0 :
    Satisfies (Magma.srch8R66 vsrch8R660) [
      311, 313, 314, 317, 318, 319, 321, 363, 365, 366, 370, 371, 372, 373, 3265, 3267, 3270,
      3273, 3274, 3275, 3277, 3280, 3283, 3285, 3287, 3289, 3290, 3291, 3294, 3295, 3299, 3300,
      3301, 3302, 3304, 3468, 3470, 3476, 3477, 3478, 3479, 3480, 3482, 3483, 3487, 3488, 3490,
      3491, 3492, 3493, 3494, 3496, 3497, 3498, 3503, 3504, 3505, 3506, 3507, 3666, 3669, 3670,
      3671, 3673, 3676, 3679, 3680, 3681, 3683, 3695, 3696, 3697, 3698, 3701, 3702, 3705, 3706,
      3707, 3708, 3710, 3866, 3869, 3875, 3876, 3881, 3882, 3884, 3885, 3886, 3889, 3894, 3896,
      3898, 3899, 3900, 3901, 3902, 3903, 3904, 3909, 3910, 3911, 3912, 3913, 4072, 4079, 4082,
      4085, 4087, 4088, 4089, 4101, 4102, 4103, 4104, 4105, 4106, 4107, 4110, 4111, 4112, 4113,
      4114, 4115, 4116, 4271, 4273, 4274, 4277, 4278, 4279, 4281, 4285, 4287, 4289, 4292, 4293,
      4294, 4295, 4296, 4298, 4299, 4300, 4301, 4302, 4303, 4305, 4306, 4308, 4309, 4310, 4311,
      4312, 4313, 4315, 4317, 4318, 4319, 4322, 4323, 4324, 4325, 4326, 4327, 4328, 4329, 4330,
      4331, 4332, 4333, 4334, 4335, 4336, 4337, 4338, 4339, 4340, 4342, 4344, 4345, 4347, 4348,
      4349, 4350, 4352, 4353, 4354, 4356, 4357, 4359, 4360, 4361, 4362, 4363, 4364, 4365, 4366,
      4367, 4368, 4370, 4371, 4372, 4373, 4374, 4375, 4376, 4377, 4378, 4379, 4384, 4386, 4387,
      4391, 4392, 4393, 4394, 4397, 4400, 4401, 4402, 4404, 4407, 4410, 4411, 4412, 4413, 4414,
      4415, 4416, 4417, 4418, 4419, 4421, 4422, 4423, 4425, 4426, 4427, 4428, 4429, 4430, 4431,
      4434, 4437, 4438, 4439, 4440, 4441, 4444, 4446, 4447, 4448, 4449, 4450, 4451, 4452, 4453,
      4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462, 4463, 4464, 4465, 4466, 4467, 4468,
      4474, 4475, 4476, 4478, 4481, 4485, 4486, 4487, 4488, 4489, 4490, 4491, 4492, 4493, 4494,
      4495, 4496, 4501, 4502, 4503, 4504, 4505, 4506, 4507, 4508, 4509, 4510, 4511, 4512, 4513,
      4514, 4515, 4516, 4517, 4518, 4519, 4520, 4521, 4522, 4523, 4524, 4525, 4526, 4527, 4528,
      4529, 4530, 4532, 4533, 4534, 4535, 4536, 4537, 4538, 4539, 4540, 4541, 4542, 4543, 4545,
      4546, 4547, 4548, 4549, 4550, 4551, 4552, 4553, 4554, 4555, 4556, 4557, 4558, 4559, 4560,
      4561, 4562, 4563, 4564, 4565, 4566, 4567, 4568, 4569, 4570, 4571, 4572, 4573, 4574, 4575,
      4576, 4577, 4578, 4579, 4580, 4581, 4582, 4586, 4588, 4589, 4593, 4594, 4595, 4596, 4600,
      4601, 4602, 4604, 4607, 4610, 4611, 4613, 4614, 4615, 4616, 4617, 4618, 4620, 4621, 4624,
      4625, 4626, 4627, 4628, 4630, 4632, 4633, 4634, 4637, 4638, 4639, 4640, 4641, 4643, 4644,
      4645, 4646, 4647, 4648, 4649, 4650, 4651, 4652, 4653, 4654, 4655, 4657, 4658, 4659, 4660,
      4661, 4662, 4663, 4664, 4665, 4667, 4668, 4669, 4670, 4671, 4672, 4673, 4674, 4675, 4676,
      4678, 4679, 4680, 4681, 4682, 4683, 4685, 4686, 4687, 4688, 4689, 4690, 4691, 4692, 4693,
      4694
    ] := by decide!

/-- `22` equations satisfied by `Magma.srch8R66 vsrch8R661`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_1 :
    Satisfies (Magma.srch8R66 vsrch8R661) [
      111, 430, 433, 434, 442, 443, 854, 1042, 1043, 1052, 1056, 1060, 1068, 1263, 1264, 1265,
      1271, 1851, 1855, 1860, 1863, 3321
    ] := by decide!

/-- `22` equations satisfied by `Magma.srch8R66 vsrch8R662`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_2 :
    Satisfies (Magma.srch8R66 vsrch8R662) [
      242, 1657, 1672, 1721, 1724, 2351, 2389, 2420, 2425, 2517, 2536, 2554, 2571, 2588, 2623,
      2712, 3093, 3142, 3145, 3180, 3197, 4175
    ] := by decide!

/-- `13` equations satisfied by `Magma.srch8R66 vsrch8R663`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_3 :
    Satisfies (Magma.srch8R66 vsrch8R663) [
      379, 3513, 3520, 3728, 3730, 3919, 3926, 4129, 4132, 4133, 4134, 4135, 4136
    ] := by decide!

/-- `13` equations satisfied by `Magma.srch8R66 vsrch8R664`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_4 :
    Satisfies (Magma.srch8R66 vsrch8R664) [
      343, 3326, 3363, 3380, 3397, 3414, 3431, 3587, 3600, 3732, 3837, 3993, 4006
    ] := by decide!

/-- `8` equations satisfied by `Magma.srch8R66 vsrch8R665`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_5 :
    Satisfies (Magma.srch8R66 vsrch8R665) [
      3355, 3417, 3588, 3601, 3994, 4007, 4154, 4162
    ] := by decide!

/-- `6` equations satisfied by `Magma.srch8R66 vsrch8R666`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_6 :
    Satisfies (Magma.srch8R66 vsrch8R666) [
      452, 455, 647, 655, 861, 1061
    ] := by decide!

/-- `6` equations satisfied by `Magma.srch8R66 vsrch8R667`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_7 :
    Satisfies (Magma.srch8R66 vsrch8R667) [
      2592, 2808, 2964, 2998, 3201, 3214
    ] := by decide!

/-- `4` equations satisfied by `Magma.srch8R66 vsrch8R668`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_8 :
    Satisfies (Magma.srch8R66 vsrch8R668) [
      3350, 3573, 3979, 4229
    ] := by decide!

/-- `2` equations satisfied by `Magma.srch8R66 vsrch8R669`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_9 :
    Satisfies (Magma.srch8R66 vsrch8R669) [
      3555, 3961
    ] := by decide!

/-- `2` equations satisfied by `Magma.srch8R66 vsrch8R6610`, and by no earlier exhibit. -/
theorem srch8R66_satisfies_10 :
    Satisfies (Magma.srch8R66 vsrch8R6610) [
      3756, 3823
    ] := by decide!
