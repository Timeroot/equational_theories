
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 3, 1], [3, 2, 2, 0], [3, 2, 2, 0], [1, 0, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 3, 1], [3, 2, 2, 0], [3, 2, 2, 0], [1, 0, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 3, 1], [3, 2, 2, 0], [3, 2, 2, 0], [1, 0, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 3, 1], [3, 2, 2, 0], [3, 2, 2, 0], [1, 0, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3331, 3364, 3526, 3556, 3880, 3924, 4026, 4146, 4216] [3, 8, 23, 38, 47, 99, 151, 203, 255, 308, 309, 310, 312, 313, 315, 323, 325, 331, 333, 335, 360, 361, 362, 364, 365, 367, 377, 378, 384, 385, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3258, 3262, 3271, 3278, 3309, 3315, 3316, 3318, 3337, 3346, 3457, 3458, 3461, 3464, 3465, 3472, 3481, 3509, 3512, 3519, 3521, 3543, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3675, 3677, 3684, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3752, 3759, 3761, 3864, 3865, 3867, 3868, 3870, 3871, 3878, 3916, 3918, 3925, 3927, 3928, 4066, 4067, 4068, 4070, 4071, 4074, 4081, 4120, 4121, 4128, 4130, 4268, 4269, 4270, 4273, 4275, 4284, 4314, 4320, 4381, 4382, 4383, 4386, 4396, 4399, 4433, 4436, 4472, 4473, 4583, 4584, 4585, 4588, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 3, 1], [3, 2, 2, 0], [3, 2, 2, 0], [1, 0, 0, 3]]», by decideFin!⟩