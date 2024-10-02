
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 3, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 3, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 3, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 3, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [343, 378, 385, 3326, 3587, 3600, 3993, 4006, 4155, 4158, 4330, 4533, 4546, 4635] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 308, 309, 310, 313, 315, 325, 326, 331, 335, 360, 361, 362, 364, 365, 367, 375, 377, 384, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3259, 3261, 3262, 3269, 3271, 3272, 3279, 3281, 3308, 3309, 3315, 3318, 3319, 3337, 3342, 3345, 3346, 3352, 3355, 3457, 3458, 3459, 3461, 3462, 3464, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3518, 3521, 3522, 3543, 3545, 3546, 3548, 3555, 3558, 3660, 3661, 3662, 3665, 3667, 3668, 3675, 3677, 3678, 3685, 3687, 3714, 3721, 3724, 3725, 3748, 3751, 3752, 3761, 3824, 3864, 3865, 3867, 3868, 3870, 3871, 3878, 3880, 3881, 3887, 3888, 3890, 3915, 3917, 3924, 3927, 3928, 3951, 3952, 3954, 3961, 3964, 4055, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4130, 4154, 4157, 4164, 4165, 4167, 4258, 4268, 4269, 4270, 4273, 4275, 4276, 4283, 4284, 4290, 4293, 4314, 4320, 4321, 4343, 4368, 4373, 4381, 4382, 4383, 4385, 4386, 4388, 4396, 4398, 4405, 4408, 4433, 4436, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4482, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4636, 4658, 4677, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 3, 2, 3]]», by decideFin!⟩