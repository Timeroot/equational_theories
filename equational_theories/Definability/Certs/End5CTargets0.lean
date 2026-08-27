import equational_theories.Definability.ExactEnd5C

/-!
# Term-structural certificate targets: `Magma.end5C`

Equations with no model among the `4` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`17` monoid of `Magma.endE5C`. `140` of them are worth listing, of which `140` appear here;
each is a valid *target* `L` of a `Magma.end5C` certificate, and so is not term-structural from any
of the `64` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`17` monoid of
`Magma.endE5C` satisfies any of these `140` equations. -/
theorem end5C_refutes_0 :
    FamilyRefutes Magma.end5C [
      9, 28, 49, 50, 51, 100, 104, 152, 166, 205, 218, 260, 280, 290, 308, 333, 364, 377, 416,
      417, 418, 419, 420, 421, 422, 423, 424, 425, 619, 620, 621, 622, 623, 624, 625, 626, 627,
      628, 819, 820, 821, 823, 829, 832, 1021, 1024, 1035, 1224, 1232, 1248, 1258, 1428, 1429,
      1430, 1478, 1630, 1634, 1681, 1691, 1701, 1833, 1837, 1838, 1839, 1884, 2036, 2050, 2124,
      2161, 2246, 2249, 2290, 2337, 2443, 2493, 2567, 2646, 2659, 2706, 2733, 2770, 2787, 2852,
      2872, 2882, 2909, 2919, 2946, 2956, 2990, 3007, 3024, 3055, 3075, 3085, 3112, 3122, 3149,
      3159, 3193, 3210, 3227, 3255, 3256, 3257, 3320, 3346, 3353, 3457, 3461, 3512, 3519, 3533,
      3546, 3660, 3674, 3721, 3759, 3864, 3877, 3918, 3921, 3925, 3927, 4070, 4090, 4100, 4120,
      4127, 4192, 4268, 4282, 4320, 4385, 4395, 4445, 4472, 4587, 4598, 4666
    ] := by nativeDecideFin!
