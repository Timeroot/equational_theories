import equational_theories.Definability.ExactEnd3L

/-!
# Term-structural certificate targets: `Magma.end3L`

Equations with no model among the `4` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`6` monoid of `Magma.endE3L`. `103` of them are worth listing, of which `103` appear here;
each is a valid *target* `L` of a `Magma.end3L` certificate, and so is not term-structural from any
of the `251` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`6` monoid of
`Magma.endE3L` satisfies any of these `103` equations. -/
theorem end3L_refutes_0 :
    FamilyRefutes Magma.end3L [
      308, 333, 364, 377, 417, 466, 500, 513, 528, 575, 617, 620, 1029, 1075, 1226, 1325, 1444,
      1451, 1455, 1632, 1654, 1691, 1838, 1840, 1921, 2043, 2053, 2137, 2267, 2327, 2457, 2540,
      2909, 2936, 3053, 3066, 3079, 3083, 3094, 3112, 3254, 3256, 3257, 3259, 3278, 3308, 3320,
      3343, 3346, 3353, 3457, 3459, 3460, 3462, 3511, 3526, 3546, 3549, 3556, 3660, 3674, 3721,
      3759, 3877, 3880, 3887, 3897, 3917, 3924, 3927, 3955, 4023, 4068, 4080, 4083, 4090, 4100,
      4120, 4127, 4130, 4158, 4192, 4268, 4275, 4282, 4283, 4286, 4291, 4307, 4320, 4385, 4395,
      4435, 4445, 4472, 4585, 4587, 4598, 4629, 4635, 4642, 4656, 4666
    ] := by nativeDecideFin!
