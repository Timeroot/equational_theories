import equational_theories.Definability.ExactEnd3K

/-!
# Term-structural certificate targets: `Magma.end3K`

Equations with no model among the `4` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`3` monoid of `Magma.endE3K`. `112` of them are worth listing, of which `112` appear here;
each is a valid *target* `L` of a `Magma.end3K` certificate, and so is not term-structural from any
of the `175` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`3` monoid of
`Magma.endE3K` satisfies any of these `112` equations. -/
theorem end3K_refutes_0 :
    FamilyRefutes Magma.end3K [
      47, 151, 153, 156, 255, 315, 362, 417, 466, 500, 513, 614, 617, 620, 622, 632, 639, 817,
      819, 825, 835, 842, 845, 848, 1075, 1226, 1325, 1426, 1428, 1431, 1434, 1441, 1444, 1451,
      1455, 1632, 1634, 1637, 1654, 1691, 1837, 1838, 1840, 1857, 1921, 2035, 2037, 2040, 2043,
      2050, 2053, 2060, 2137, 2267, 2327, 2457, 2644, 2652, 2659, 2662, 2669, 2672, 2687, 2847,
      2855, 2865, 2872, 2909, 2936, 3053, 3066, 3079, 3112, 3474, 3484, 3556, 3659, 3660, 3661,
      3664, 3667, 3668, 3674, 3687, 3712, 3714, 3721, 3725, 3752, 3759, 3868, 3871, 3924, 4380,
      4382, 4383, 4385, 4395, 4396, 4399, 4403, 4409, 4420, 4432, 4433, 4435, 4438, 4445, 4470,
      4472, 4473, 4480
    ] := by nativeDecideFin!
