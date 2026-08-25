import equational_theories.Definability.ExactEnd3G

/-!
# Term-structural certificate targets: `Magma.end3G`

Equations with no model among the `2` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`7` monoid of `Magma.endE3G`. `108` of them are worth listing, of which `108` appear here;
each is a valid *target* `L` of a `Magma.end3G` certificate, and so is not term-structural from any
of the `448` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`7` monoid of
`Magma.endE3G` satisfies any of these `108` equations. -/
theorem end3G_refutes_0 :
    FamilyRefutes Magma.end3G [
      10, 25, 52, 107, 110, 153, 156, 211, 214, 257, 309, 323, 361, 378, 426, 432, 439, 629, 639,
      835, 842, 848, 1038, 1041, 1048, 1051, 1059, 1063, 1067, 1241, 1244, 1251, 1254, 1262,
      1266, 1270, 1431, 1437, 1441, 1637, 1640, 1644, 1650, 1834, 1853, 1857, 1867, 2037, 2040,
      2070, 2256, 2259, 2266, 2269, 2277, 2281, 2285, 2459, 2462, 2469, 2472, 2480, 2484, 2488,
      2652, 2662, 2687, 2849, 2855, 3052, 3071, 3078, 3258, 3264, 3308, 3309, 3343, 3464, 3467,
      3509, 3511, 3661, 3664, 3712, 3725, 3870, 3873, 3928, 3955, 4067, 4076, 4121, 4130, 4158,
      4269, 4283, 4284, 4291, 4316, 4382, 4396, 4432, 4473, 4584, 4599, 4629, 4631, 4635
    ] := by nativeDecideFin!
