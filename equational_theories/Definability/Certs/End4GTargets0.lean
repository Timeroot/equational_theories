import equational_theories.Definability.ExactEnd4G

/-!
# Term-structural certificate targets: `Magma.end4G`

Equations with no model among the `24` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`8` monoid of `Magma.endE4G`. `138` of them are worth listing, of which `138` appear here;
each is a valid *target* `L` of a `Magma.end4G` certificate, and so is not term-structural from any
of the `58` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `24` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`8` monoid of
`Magma.endE4G` satisfies any of these `138` equations. -/
theorem end4G_refutes_0 :
    FamilyRefutes Magma.end4G [
      9, 28, 49, 50, 51, 100, 102, 152, 166, 218, 228, 260, 280, 290, 308, 364, 416, 417, 418,
      420, 421, 422, 423, 424, 425, 429, 436, 617, 618, 620, 621, 622, 623, 624, 625, 626, 627,
      628, 819, 820, 821, 823, 826, 1021, 1024, 1026, 1029, 1045, 1224, 1226, 1231, 1232, 1428,
      1429, 1430, 1478, 1630, 1632, 1654, 1681, 1691, 1701, 1833, 1838, 1839, 1840, 1884, 1921,
      2036, 2050, 2124, 2161, 2263, 2290, 2327, 2337, 2449, 2493, 2503, 2540, 2567, 2659, 2706,
      2733, 2743, 2770, 2872, 2882, 2909, 2919, 2936, 2946, 2956, 2973, 2990, 3007, 3024, 3055,
      3058, 3068, 3085, 3112, 3122, 3149, 3159, 3193, 3210, 3227, 3255, 3256, 3257, 3261, 3316,
      3318, 3320, 3457, 3459, 3519, 3533, 3660, 3674, 3877, 3887, 3921, 3925, 4070, 4073, 4090,
      4100, 4128, 4155, 4192, 4268, 4282, 4385, 4395, 4587, 4666
    ] := by nativeDecideFin!
