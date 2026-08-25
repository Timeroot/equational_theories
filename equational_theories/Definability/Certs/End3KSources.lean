import equational_theories.Definability.ExactEnd3K

/-!
# Term-structural certificate sources: `Magma.end3K`

For each of the following magmas, drawn from the `4` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`3` monoid of `Magma.endE3K`, the equations it satisfies that no earlier listed
magma does. Together they are the `175` equations that are worth using as the *source* `L'` of a
`Magma.end3K` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `79` equations satisfied by `Magma.end3K 0`, and by no earlier member of the cover. -/
theorem end3K_satisfies_0 :
    Satisfies (Magma.end3K 0) [
      39, 45, 388, 391, 399, 403, 407, 3284, 3292, 3296, 3300, 3349, 3356, 3359, 3363, 3367,
      3371, 3375, 3380, 3384, 3388, 3392, 3397, 3401, 3405, 3409, 3418, 3422, 3426, 3431, 3436,
      3441, 3446, 3451, 3958, 3965, 3968, 3976, 3980, 3984, 4001, 4010, 4014, 4018, 4027, 4031,
      4035, 4045, 4050, 4055, 4060, 4161, 4168, 4171, 4179, 4183, 4187, 4196, 4204, 4213, 4217,
      4221, 4230, 4234, 4238, 4248, 4253, 4258, 4263, 4278, 4296, 4304, 4310, 4323, 4334, 4348,
      4354, 4367, 4378
    ] := by decide!

/-- `79` equations satisfied by `Magma.end3K 2`, and by no earlier member of the cover. -/
theorem end3K_satisfies_1 :
    Satisfies (Magma.end3K 2) [
      38, 42, 322, 324, 328, 330, 331, 3305, 3307, 3310, 3311, 3313, 3314, 3325, 3327, 3328,
      3329, 3332, 3333, 3335, 3336, 3337, 3339, 3340, 3341, 3508, 3510, 3514, 3516, 3517, 3528,
      3530, 3531, 3532, 3535, 3536, 3538, 3539, 3540, 3542, 3543, 3544, 4075, 4077, 4078, 4079,
      4117, 4119, 4122, 4123, 4125, 4126, 4129, 4132, 4133, 4136, 4137, 4139, 4140, 4141, 4143,
      4144, 4145, 4147, 4148, 4149, 4151, 4152, 4153, 4586, 4600, 4603, 4604, 4632, 4633, 4634,
      4657, 4674, 4676
    ] := by decide!

/-- `9` equations satisfied by `Magma.end3K 1`, and by no earlier member of the cover. -/
theorem end3K_satisfies_2 :
    Satisfies (Magma.end3K 1) [
      107, 110, 416, 422, 442, 446, 450, 454, 458
    ] := by decide!

/-- `8` equations satisfied by `Magma.end3K 3`, and by no earlier member of the cover. -/
theorem end3K_satisfies_3 :
    Satisfies (Magma.end3K 3) [
      25, 3055, 3061, 3081, 3085, 3089, 3093, 3097
    ] := by decide!
