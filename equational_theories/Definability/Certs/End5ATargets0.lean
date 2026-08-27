import equational_theories.Definability.ExactEnd5A

/-!
# Term-structural certificate targets: `Magma.end5A`

Equations with no model among the `98` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`9` monoid of `Magma.endE5A`. `120` of them are worth listing, of which `120` appear here;
each is a valid *target* `L` of a `Magma.end5A` certificate, and so is not term-structural from any
of the `249` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `98` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`9` monoid of
`Magma.endE5A` satisfies any of these `120` equations. -/
theorem end5A_refutes_0 :
    FamilyRefutes Magma.end5A [
      16, 26, 43, 127, 160, 179, 212, 325, 327, 385, 395, 417, 452, 466, 473, 500, 513, 528, 562,
      575, 632, 825, 833, 1026, 1061, 1075, 1109, 1122, 1184, 1229, 1264, 1278, 1325, 1432, 1455,
      1645, 1655, 1658, 1662, 1701, 1721, 1780, 1839, 1851, 1873, 1887, 1897, 1934, 1949, 2097,
      2137, 2254, 2267, 2300, 2389, 2444, 2457, 2470, 2485, 2503, 2592, 2669, 2699, 2865, 3053,
      3056, 3066, 3079, 3083, 3091, 3094, 3112, 3201, 3317, 3318, 3320, 3321, 3324, 3334, 3343,
      3346, 3388, 3414, 3520, 3523, 3524, 3526, 3527, 3533, 3667, 3675, 3703, 3714, 3752, 3921,
      3972, 3989, 4006, 4023, 4040, 4120, 4130, 4135, 4143, 4146, 4155, 4175, 4192, 4209, 4243,
      4315, 4339, 4357, 4362, 4531, 4544, 4615, 4645, 4673, 4689
    ] := by nativeDecideFin!
