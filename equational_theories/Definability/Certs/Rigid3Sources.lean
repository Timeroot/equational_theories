import equational_theories.Definability.StructuralRigid3

/-!
# Structural certificate sources: `Magma.rigid3`

For each of the following magmas, drawn from the `19422` rigid magmas on `Fin 3`, the equations it
satisfies that no earlier listed magma does. Every one of the `1776` equations with a rigid model on
`Fin 3` appears in exactly one of these lists, so they are exactly the laws that can be used as the
*source* `L'` of a `Magma.rigid3` certificate. `42` members cover them all.

This file is generated; see the module docstring of `Definability.StructuralRigid3`.
-/

set_option maxHeartbeats 1000000

/-- `493` equations satisfied by `Magma.rigid3 0 0 0 0 0 0 0 1 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_0 :
    Satisfies (Magma.rigid3 0 0 0 0 0 0 0 1 0) [
      1, 40, 307, 309, 310, 312, 313, 316, 319, 320, 323, 359, 360, 361, 362, 363, 364, 365, 366,
      367, 368, 369, 370, 371, 372, 373, 3253, 3255, 3256, 3258, 3259, 3261, 3262, 3264, 3265,
      3266, 3268, 3269, 3271, 3272, 3274, 3275, 3276, 3278, 3279, 3282, 3285, 3286, 3288, 3289,
      3290, 3293, 3294, 3297, 3298, 3301, 3302, 3303, 3306, 3456, 3457, 3458, 3459, 3460, 3461,
      3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476,
      3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491,
      3492, 3493, 3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506,
      3507, 3659, 3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668, 3669, 3670, 3671, 3672,
      3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680, 3681, 3682, 3683, 3684, 3685, 3686, 3687,
      3688, 3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702,
      3703, 3704, 3705, 3706, 3707, 3708, 3709, 3710, 3862, 3863, 3864, 3865, 3866, 3867, 3868,
      3869, 3870, 3871, 3872, 3873, 3874, 3875, 3876, 3877, 3878, 3879, 3880, 3881, 3882, 3883,
      3884, 3885, 3886, 3887, 3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895, 3896, 3897, 3898,
      3899, 3900, 3901, 3902, 3903, 3904, 3905, 3906, 3907, 3908, 3909, 3910, 3911, 3912, 3913,
      4065, 4066, 4067, 4068, 4069, 4070, 4071, 4072, 4073, 4074, 4075, 4076, 4077, 4078, 4079,
      4080, 4081, 4082, 4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094,
      4095, 4096, 4097, 4098, 4099, 4100, 4101, 4102, 4103, 4104, 4105, 4106, 4107, 4108, 4109,
      4110, 4111, 4112, 4113, 4114, 4115, 4116, 4269, 4270, 4272, 4273, 4276, 4279, 4280, 4314,
      4316, 4318, 4320, 4321, 4324, 4325, 4327, 4331, 4332, 4336, 4337, 4341, 4343, 4346, 4351,
      4355, 4362, 4380, 4381, 4382, 4383, 4384, 4385, 4386, 4387, 4388, 4389, 4390, 4391, 4392,
      4393, 4394, 4432, 4433, 4434, 4435, 4436, 4437, 4438, 4439, 4440, 4441, 4442, 4443, 4444,
      4445, 4446, 4447, 4448, 4449, 4450, 4451, 4452, 4453, 4454, 4455, 4456, 4457, 4458, 4459,
      4460, 4461, 4462, 4463, 4464, 4465, 4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473, 4474,
      4475, 4476, 4477, 4478, 4479, 4480, 4481, 4482, 4483, 4484, 4485, 4486, 4487, 4488, 4489,
      4490, 4491, 4492, 4493, 4494, 4495, 4496, 4497, 4498, 4499, 4500, 4501, 4502, 4503, 4504,
      4505, 4583, 4584, 4585, 4586, 4587, 4588, 4589, 4590, 4591, 4592, 4593, 4594, 4595, 4596,
      4597, 4598, 4599, 4600, 4601, 4602, 4603, 4604, 4605, 4606, 4607, 4608, 4609, 4610, 4611,
      4612, 4613, 4614, 4615, 4616, 4617, 4618, 4619, 4620, 4621, 4622, 4623, 4624, 4625, 4626,
      4627, 4628, 4629, 4630, 4631, 4632, 4633, 4634, 4635, 4636, 4637, 4638, 4639, 4640, 4641,
      4642, 4643, 4644, 4645, 4646, 4647, 4648, 4649, 4650, 4651, 4652, 4653, 4654, 4655, 4656,
      4657, 4658, 4659, 4660, 4661, 4662, 4663, 4664, 4665, 4666, 4667, 4668, 4669, 4670, 4671,
      4672, 4673, 4674, 4675, 4676, 4677, 4678, 4679, 4680, 4681, 4682, 4683, 4684, 4685, 4686,
      4687, 4688, 4689, 4690, 4691, 4692, 4693, 4694
    ] := by decide!

/-- `260` equations satisfied by `Magma.rigid3 0 0 0 0 0 0 2 2 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_1 :
    Satisfies (Magma.rigid3 0 0 0 0 0 0 2 2 2) [
      38, 42, 308, 311, 322, 324, 325, 326, 327, 328, 329, 330, 331, 374, 375, 376, 377, 378,
      379, 380, 381, 382, 383, 3254, 3257, 3260, 3263, 3267, 3305, 3307, 3308, 3309, 3310, 3311,
      3312, 3313, 3314, 3315, 3316, 3317, 3318, 3319, 3320, 3321, 3322, 3323, 3324, 3325, 3326,
      3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340, 3341,
      3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520, 3521, 3522,
      3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537,
      3538, 3539, 3540, 3541, 3542, 3543, 3544, 3711, 3712, 3713, 3714, 3715, 3716, 3717, 3718,
      3719, 3720, 3721, 3722, 3723, 3724, 3725, 3726, 3727, 3728, 3729, 3730, 3731, 3732, 3733,
      3734, 3735, 3736, 3737, 3738, 3739, 3740, 3741, 3742, 3743, 3744, 3745, 3746, 3747, 3914,
      3915, 3916, 3917, 3918, 3919, 3920, 3921, 3922, 3923, 3924, 3925, 3926, 3927, 3928, 3929,
      3930, 3931, 3932, 3933, 3934, 3935, 3936, 3937, 3938, 3939, 3940, 3941, 3942, 3943, 3944,
      3945, 3946, 3947, 3948, 3949, 3950, 4117, 4118, 4119, 4120, 4121, 4122, 4123, 4124, 4125,
      4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140,
      4141, 4142, 4143, 4144, 4145, 4146, 4147, 4148, 4149, 4150, 4151, 4152, 4153, 4268, 4271,
      4282, 4283, 4284, 4285, 4286, 4287, 4288, 4289, 4315, 4317, 4319, 4339, 4340, 4342, 4357,
      4358, 4359, 4360, 4361, 4395, 4396, 4397, 4398, 4399, 4400, 4401, 4402, 4403, 4404, 4506,
      4507, 4508, 4509, 4510, 4511, 4512, 4513, 4514, 4515, 4516, 4517, 4518, 4519, 4520, 4521,
      4522
    ] := by decide!

/-- `194` equations satisfied by `Magma.rigid3 0 0 2 0 0 2 0 0 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_2 :
    Satisfies (Magma.rigid3 0 0 2 0 0 2 0 0 2) [
      39, 45, 315, 318, 333, 336, 339, 343, 347, 351, 355, 385, 388, 391, 395, 399, 403, 407,
      3281, 3284, 3292, 3296, 3300, 3343, 3346, 3349, 3353, 3356, 3359, 3363, 3367, 3371, 3375,
      3380, 3384, 3388, 3392, 3397, 3401, 3405, 3409, 3414, 3418, 3422, 3426, 3431, 3436, 3441,
      3446, 3451, 3546, 3549, 3552, 3556, 3559, 3562, 3566, 3570, 3574, 3578, 3583, 3587, 3591,
      3595, 3600, 3604, 3608, 3612, 3617, 3621, 3625, 3629, 3634, 3639, 3644, 3649, 3654, 3749,
      3752, 3755, 3759, 3762, 3765, 3769, 3773, 3777, 3781, 3786, 3790, 3794, 3798, 3803, 3807,
      3811, 3815, 3820, 3824, 3828, 3832, 3837, 3842, 3847, 3852, 3857, 3952, 3955, 3958, 3962,
      3965, 3968, 3972, 3976, 3980, 3984, 3989, 3993, 3997, 4001, 4006, 4010, 4014, 4018, 4023,
      4027, 4031, 4035, 4040, 4045, 4050, 4055, 4060, 4155, 4158, 4161, 4165, 4168, 4171, 4175,
      4179, 4183, 4187, 4192, 4196, 4200, 4204, 4209, 4213, 4217, 4221, 4226, 4230, 4234, 4238,
      4243, 4248, 4253, 4258, 4263, 4275, 4278, 4291, 4296, 4300, 4304, 4307, 4310, 4323, 4330,
      4334, 4348, 4354, 4367, 4374, 4378, 4406, 4409, 4412, 4416, 4420, 4424, 4428, 4525, 4529,
      4533, 4537, 4542, 4546, 4550, 4554, 4559, 4564, 4569, 4574, 4579
    ] := by decide!

/-- `142` equations satisfied by `Magma.rigid3 0 0 0 1 0 1 2 2 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_3 :
    Satisfies (Magma.rigid3 0 0 0 1 0 1 2 2 2) [
      8, 10, 11, 99, 100, 101, 104, 105, 106, 107, 108, 109, 110, 111, 411, 413, 414, 426, 427,
      429, 430, 432, 433, 434, 436, 437, 439, 440, 442, 443, 444, 817, 818, 819, 820, 821, 823,
      832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849,
      850, 851, 854, 858, 1020, 1022, 1023, 1025, 1028, 1031, 1035, 1036, 1038, 1039, 1041, 1042,
      1043, 1045, 1046, 1048, 1049, 1051, 1052, 1053, 1055, 1056, 1059, 1060, 1063, 1064, 1067,
      1068, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1234, 1238, 1239, 1240, 1241,
      1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256,
      1257, 1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1270, 1271, 1832, 1834,
      1835, 1847, 1850, 1851, 1853, 1855, 1857, 1860, 1861, 1863, 1865
    ] := by decide!

/-- `142` equations satisfied by `Magma.rigid3 0 1 2 0 0 2 0 1 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_4 :
    Satisfies (Magma.rigid3 0 1 2 0 0 2 0 1 2) [
      23, 25, 31, 203, 205, 208, 211, 214, 218, 221, 224, 231, 242, 246, 1629, 1631, 1637, 1644,
      1647, 1650, 1657, 1672, 1718, 1721, 1724, 1731, 1746, 2238, 2240, 2243, 2246, 2249, 2253,
      2256, 2259, 2263, 2266, 2269, 2273, 2277, 2281, 2285, 2290, 2293, 2296, 2300, 2303, 2306,
      2310, 2314, 2318, 2322, 2327, 2330, 2333, 2340, 2351, 2355, 2364, 2368, 2372, 2376, 2385,
      2389, 2402, 2406, 2420, 2425, 2430, 2441, 2443, 2446, 2449, 2452, 2456, 2459, 2462, 2466,
      2469, 2472, 2476, 2480, 2484, 2488, 2496, 2506, 2517, 2530, 2533, 2536, 2543, 2554, 2558,
      2571, 2588, 2605, 2623, 2644, 2646, 2652, 2659, 2662, 2665, 2672, 2687, 2696, 2699, 2702,
      2706, 2709, 2712, 2724, 2733, 2736, 2739, 2746, 2761, 2770, 2774, 2778, 2782, 2791, 2795,
      2812, 2836, 3050, 3052, 3058, 3065, 3068, 3071, 3078, 3093, 3105, 3115, 3139, 3142, 3145,
      3152, 3167, 3180, 3197
    ] := by decide!

/-- `118` equations satisfied by `Magma.rigid3 0 0 0 0 0 0 0 0 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_5 :
    Satisfies (Magma.rigid3 0 0 0 0 0 0 0 0 1) [
      43, 4274, 4277, 4281, 4290, 4292, 4293, 4294, 4295, 4297, 4298, 4299, 4301, 4302, 4303,
      4305, 4306, 4308, 4309, 4311, 4312, 4313, 4322, 4326, 4328, 4329, 4333, 4335, 4338, 4344,
      4345, 4347, 4349, 4350, 4352, 4353, 4356, 4363, 4364, 4365, 4366, 4368, 4369, 4370, 4371,
      4372, 4373, 4375, 4376, 4377, 4379, 4405, 4407, 4408, 4410, 4411, 4413, 4414, 4415, 4417,
      4418, 4419, 4421, 4422, 4423, 4425, 4426, 4427, 4429, 4430, 4431, 4523, 4524, 4526, 4527,
      4528, 4530, 4531, 4532, 4534, 4535, 4536, 4538, 4539, 4540, 4541, 4543, 4544, 4545, 4547,
      4548, 4549, 4551, 4552, 4553, 4555, 4556, 4557, 4558, 4560, 4561, 4562, 4563, 4565, 4566,
      4567, 4568, 4570, 4571, 4572, 4573, 4575, 4576, 4577, 4578, 4580, 4581, 4582
    ] := by decide!

/-- `78` equations satisfied by `Magma.rigid3 0 0 0 1 1 0 2 2 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_6 :
    Satisfies (Magma.rigid3 0 0 0 1 1 0 2 2 2) [
      3, 9, 47, 48, 49, 50, 51, 102, 103, 151, 152, 255, 412, 415, 416, 417, 418, 419, 420, 421,
      422, 423, 424, 425, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627,
      628, 822, 824, 825, 826, 827, 828, 829, 830, 831, 1021, 1024, 1026, 1027, 1029, 1030, 1032,
      1033, 1034, 1232, 1233, 1235, 1236, 1237, 1426, 1427, 1428, 1429, 1430, 1630, 1632, 1633,
      1833, 1837, 1838, 1839, 2035, 2036, 2847, 2852
    ] := by decide!

/-- `68` equations satisfied by `Magma.rigid3 0 1 1 0 1 2 0 1 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_7 :
    Satisfies (Magma.rigid3 0 1 1 0 1 2 0 1 2) [
      28, 166, 228, 238, 260, 270, 280, 290, 1478, 1634, 1681, 1691, 1701, 1884, 1921, 1958,
      2050, 2087, 2124, 2161, 2337, 2347, 2381, 2398, 2415, 2493, 2503, 2513, 2540, 2550, 2567,
      2584, 2601, 2618, 2649, 2669, 2679, 2716, 2743, 2753, 2787, 2804, 2821, 2862, 2872, 2882,
      2899, 2909, 2919, 2936, 2946, 2956, 2973, 2990, 3007, 3024, 3055, 3075, 3085, 3102, 3112,
      3122, 3149, 3159, 3176, 3193, 3210, 3227
    ] := by decide!

/-- `46` equations satisfied by `Magma.rigid3 0 0 0 1 1 2 2 2 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_8 :
    Satisfies (Magma.rigid3 0 0 0 1 1 2 2 2 1) [
      26, 630, 632, 639, 643, 647, 1442, 1451, 1455, 1459, 1645, 1654, 1658, 1662, 1873, 2038,
      2041, 2051, 2060, 2064, 2068, 2241, 2254, 2267, 2282, 2444, 2447, 2457, 2470, 2485, 2647,
      2660, 2673, 2688, 2850, 2853, 2855, 2876, 2880, 3053, 3056, 3066, 3079, 3083, 3091, 3094
    ] := by decide!

/-- `45` equations satisfied by `Magma.rigid3 0 0 2 0 0 2 2 2 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_9 :
    Satisfies (Magma.rigid3 0 0 2 0 0 2 2 2 0) [
      3342, 3350, 3355, 3364, 3370, 3385, 3398, 3404, 3417, 3545, 3553, 3558, 3567, 3573, 3588,
      3601, 3607, 3620, 3748, 3756, 3761, 3770, 3776, 3791, 3804, 3810, 3823, 3951, 3959, 3964,
      3973, 3979, 3994, 4007, 4013, 4026, 4154, 4162, 4167, 4176, 4182, 4197, 4210, 4216, 4229
    ] := by decide!

/-- `44` equations satisfied by `Magma.rigid3 0 1 2 0 1 2 0 2 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_10 :
    Satisfies (Magma.rigid3 0 1 2 0 1 2 0 2 1) [
      16, 466, 473, 500, 513, 528, 562, 575, 676, 703, 716, 731, 872, 906, 919, 981, 1075, 1082,
      1109, 1122, 1184, 1278, 1312, 1325, 1387, 1434, 1481, 1488, 1515, 1528, 1543, 1780, 1840,
      1887, 1934, 1949, 2043, 2090, 2137, 2152, 2865, 2902, 2949, 2964
    ] := by decide!

/-- `24` equations satisfied by `Magma.rigid3 0 0 0 1 1 2 1 1 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_11 :
    Satisfies (Magma.rigid3 0 0 0 1 1 2 1 1 2) [
      156, 257, 263, 266, 1441, 1867, 2040, 2070, 2655, 2675, 2683, 2691, 2849, 2858, 2868, 2875,
      2878, 2886, 2890, 2894, 3061, 3081, 3089, 3097
    ] := by decide!

/-- `24` equations satisfied by `Magma.rigid3 0 0 2 1 1 2 0 0 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_12 :
    Satisfies (Magma.rigid3 0 0 2 1 1 2 0 0 2) [
      52, 55, 58, 153, 446, 450, 454, 458, 629, 635, 642, 645, 649, 653, 657, 661, 852, 856, 860,
      864, 1431, 1437, 1640, 2037
    ] := by decide!

/-- `14` equations satisfied by `Magma.rigid3 0 0 0 0 0 0 0 0 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_13 :
    Satisfies (Magma.rigid3 0 0 0 0 0 0 0 0 2) [
      332, 335, 384, 387, 3345, 3352, 3548, 3555, 3751, 3758, 3954, 3961, 4157, 4164
    ] := by decide!

/-- `13` equations satisfied by `Magma.rigid3 0 0 0 0 0 0 0 2 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_14 :
    Satisfies (Magma.rigid3 0 0 0 0 0 0 0 2 0) [
      314, 317, 321, 3270, 3273, 3277, 3280, 3283, 3287, 3291, 3295, 3299, 3304
    ] := by decide!

/-- `12` equations satisfied by `Magma.rigid3 0 0 0 2 2 1 1 1 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_15 :
    Satisfies (Magma.rigid3 0 0 0 2 2 1 1 1 1) [
      1435, 1444, 1445, 1446, 1448, 1638, 1660, 1848, 1858, 1868, 1869, 1871
    ] := by decide!

/-- `12` equations satisfied by `Magma.rigid3 0 2 1 0 2 1 0 1 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_16 :
    Satisfies (Magma.rigid3 0 2 1 0 2 1 0 1 1) [
      1668, 1684, 1694, 1697, 1705, 1875, 1931, 2053, 2127, 2134, 2165, 2169
    ] := by decide!

/-- `8` equations satisfied by `Magma.rigid3 0 0 2 1 1 2 2 2 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_17 :
    Satisfies (Magma.rigid3 0 0 2 1 1 2 2 2 0) [
      452, 455, 655, 658, 861, 1061, 1432, 1635
    ] := by decide!

/-- `8` equations satisfied by `Magma.rigid3 0 1 2 0 1 2 2 2 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_18 :
    Satisfies (Magma.rigid3 0 1 2 0 1 2 2 2 0) [
      1894, 2097, 2592, 2808, 2998, 3011, 3201, 3214
    ] := by decide!

/-- `4` equations satisfied by `Magma.rigid3 0 1 2 1 0 0 2 1 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_19 :
    Satisfies (Magma.rigid3 0 1 2 1 0 0 2 1 0) [
      1519, 1523, 2128, 2132
    ] := by decide!

/-- `4` equations satisfied by `Magma.rigid3 1 0 1 0 0 2 1 2 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_20 :
    Satisfies (Magma.rigid3 1 0 1 0 0 2 1 2 1) [
      1479, 1482, 2088, 2125
    ] := by decide!

/-- `2` equations satisfied by `Magma.rigid3 0 0 1 2 0 2 1 1 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_21 :
    Satisfies (Magma.rigid3 0 0 1 2 0 2 1 1 0) [
      1841, 1845
    ] := by decide!

/-- `2` equations satisfied by `Magma.rigid3 0 2 1 0 0 1 1 2 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_22 :
    Satisfies (Magma.rigid3 0 2 1 0 0 1 1 2 0) [
      1728, 1738
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 0 2 2 0 1 1 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_23 :
    Satisfies (Magma.rigid3 0 0 0 2 2 0 1 1 1) [
      1641
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 1 1 1 2 2 2 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_24 :
    Satisfies (Magma.rigid3 0 0 1 1 1 2 2 2 0) [
      264
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 1 1 2 0 2 0 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_25 :
    Satisfies (Magma.rigid3 0 0 1 1 2 0 2 0 1) [
      56
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 1 1 2 0 2 2 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_26 :
    Satisfies (Magma.rigid3 0 0 1 1 2 0 2 2 1) [
      159
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 1 1 2 1 1 2 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_27 :
    Satisfies (Magma.rigid3 0 0 1 1 2 1 1 2 1) [
      1843
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 1 2 0 0 1 2 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_28 :
    Satisfies (Magma.rigid3 0 0 1 2 0 0 1 2 2) [
      1454
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 1 2 0 1 0 0 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_29 :
    Satisfies (Magma.rigid3 0 0 1 2 0 1 0 0 1) [
      1484
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 1 2 1 2 0 2 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_30 :
    Satisfies (Magma.rigid3 0 0 1 2 1 2 0 2 1) [
      1682
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 1 2 2 1 0 1 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_31 :
    Satisfies (Magma.rigid3 0 0 1 2 2 1 0 1 2) [
      1885
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 1 2 2 2 0 0 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_32 :
    Satisfies (Magma.rigid3 0 0 1 2 2 2 0 0 0) [
      2052
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 2 2 1 0 1 1 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_33 :
    Satisfies (Magma.rigid3 0 0 2 2 1 0 1 1 0) [
      1897
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 0 2 2 2 1 1 0 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_34 :
    Satisfies (Magma.rigid3 0 0 2 2 2 1 1 0 0) [
      1655
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 1 1 0 2 1 1 2 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_35 :
    Satisfies (Magma.rigid3 0 1 1 0 2 1 1 2 1) [
      1664
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 1 2 0 1 2 1 2 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_36 :
    Satisfies (Magma.rigid3 0 1 2 0 1 2 1 2 0) [
      75
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 1 2 0 2 0 1 0 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_37 :
    Satisfies (Magma.rigid3 0 1 2 0 2 0 1 0 1) [
      283
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 2 1 0 0 2 1 0 2`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_38 :
    Satisfies (Magma.rigid3 0 2 1 0 0 2 1 0 2) [
      2063
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 0 2 1 0 2 0 0 2 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_39 :
    Satisfies (Magma.rigid3 0 2 1 0 2 0 0 2 1) [
      1975
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 1 0 2 2 0 0 0 2 1`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_40 :
    Satisfies (Magma.rigid3 1 0 2 2 0 0 0 2 1) [
      1685
    ] := by decide!

/-- `1` equations satisfied by `Magma.rigid3 1 1 2 2 0 1 1 2 0`, and by no earlier member of the
cover. -/
theorem rigid3_satisfies_41 :
    Satisfies (Magma.rigid3 1 1 2 2 0 1 1 2 0) [
      1922
    ] := by decide!
