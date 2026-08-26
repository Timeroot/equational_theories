import equational_theories.Definability.ExactEnd4D

/-!
# Term-structural certificate targets: `Magma.end4D`

Equations with no model among the `2` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`16` monoid of `Magma.endE4D`. `132` of them are worth listing, of which `132` appear here;
each is a valid *target* `L` of a `Magma.end4D` certificate, and so is not term-structural from any
of the `12` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`16` monoid of
`Magma.endE4D` satisfies any of these `132` equations. -/
theorem end4D_refutes_0 :
    FamilyRefutes Magma.end4D [
      117, 127, 152, 160, 166, 179, 209, 212, 308, 333, 364, 377, 466, 473, 500, 513, 528, 575,
      1075, 1278, 1288, 1325, 1370, 1427, 1429, 1430, 1442, 1443, 1452, 1453, 1455, 1456, 1630,
      1632, 1633, 1635, 1681, 1684, 1691, 1701, 1833, 1838, 1839, 1848, 1884, 1894, 1921, 1958,
      2087, 2090, 2093, 2100, 2115, 2124, 2137, 2161, 2203, 2254, 2264, 2267, 2270, 2457, 3053,
      3056, 3066, 3079, 3083, 3094, 3254, 3256, 3257, 3259, 3318, 3320, 3343, 3346, 3353, 3457,
      3459, 3460, 3462, 3511, 3518, 3521, 3526, 3546, 3549, 3660, 3674, 3721, 3759, 3877, 3880,
      3887, 3897, 3917, 3927, 3952, 3955, 3962, 4023, 4080, 4083, 4090, 4100, 4120, 4127, 4130,
      4155, 4192, 4268, 4275, 4282, 4283, 4286, 4291, 4307, 4314, 4320, 4385, 4395, 4445, 4472,
      4585, 4587, 4598, 4606, 4629, 4635, 4642, 4656, 4666
    ] := by nativeDecideFin!
