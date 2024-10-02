
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 3, 2, 3], [3, 2, 2, 3], [0, 1, 2, 3], [0, 1, 2, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 3, 2, 3], [3, 2, 2, 3], [0, 1, 2, 3], [0, 1, 2, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 3, 2, 3], [3, 2, 2, 3], [0, 1, 2, 3], [0, 1, 2, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 3, 2, 3], [3, 2, 2, 3], [0, 1, 2, 3], [0, 1, 2, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 25, 31, 205, 208, 221, 246, 316, 323, 1647, 1672, 1724, 1731, 2285, 2306, 2310, 2314, 2372, 2430, 2488, 2530, 2554, 2571, 2588, 2702, 2712, 2739, 2774, 2778, 3068, 3093, 3145, 3180, 3197, 3488, 3496, 3500, 3509, 3519, 4098, 4105, 4128, 4155, 4165, 4321, 4355, 4611] [2, 3, 8, 24, 26, 29, 38, 39, 43, 47, 99, 151, 204, 206, 209, 212, 219, 222, 224, 228, 229, 242, 255, 308, 309, 313, 315, 325, 326, 331, 333, 335, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1630, 1632, 1634, 1635, 1638, 1645, 1648, 1654, 1655, 1658, 1681, 1682, 1684, 1685, 1691, 1692, 1694, 1695, 1719, 1722, 1728, 1729, 1832, 2035, 2239, 2241, 2244, 2247, 2254, 2257, 2264, 2267, 2291, 2294, 2296, 2301, 2304, 2328, 2331, 2333, 2337, 2338, 2351, 2368, 2389, 2402, 2442, 2444, 2447, 2450, 2457, 2460, 2467, 2470, 2493, 2494, 2497, 2503, 2504, 2507, 2517, 2531, 2534, 2536, 2540, 2541, 2558, 2645, 2647, 2649, 2650, 2653, 2660, 2663, 2665, 2669, 2670, 2673, 2697, 2700, 2707, 2710, 2734, 2737, 2743, 2744, 2847, 3051, 3053, 3055, 3056, 3059, 3066, 3069, 3075, 3076, 3079, 3102, 3103, 3106, 3112, 3113, 3116, 3140, 3143, 3149, 3150, 3254, 3255, 3259, 3261, 3269, 3271, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3337, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3457, 3459, 3462, 3465, 3467, 3471, 3474, 3478, 3481, 3484, 3492, 3511, 3512, 3518, 3521, 3529, 3543, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3660, 3661, 3667, 3675, 3685, 3687, 3714, 3719, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3761, 3824, 3862, 4055, 4066, 4067, 4071, 4073, 4074, 4080, 4081, 4083, 4091, 4093, 4120, 4121, 4127, 4130, 4131, 4157, 4158, 4164, 4167, 4175, 4258, 4268, 4269, 4273, 4275, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[2, 3, 2, 3], [3, 2, 2, 3], [0, 1, 2, 3], [0, 1, 2, 2]]», by decideFin!⟩