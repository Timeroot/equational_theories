import equational_theories.Definability.ExactEnd4A

/-!
# Term-structural certificate targets: `Magma.end4A`

Equations with no model among the `2` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`16` monoid of `Magma.endE4A`. `104` of them are worth listing, of which `104` appear here;
each is a valid *target* `L` of a `Magma.end4A` certificate, and so is not term-structural from any
of the `2` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`16` monoid of
`Magma.endE4A` satisfies any of these `104` equations. -/
theorem end4A_refutes_0 :
    FamilyRefutes Magma.end4A [
      47, 50, 100, 218, 255, 280, 315, 362, 414, 417, 614, 615, 617, 620, 622, 623, 624, 632,
      639, 703, 817, 818, 819, 820, 821, 823, 825, 835, 842, 845, 848, 1021, 1023, 1026, 1224,
      1226, 1227, 1229, 2290, 2300, 2327, 2364, 2493, 2503, 2530, 2644, 2652, 2659, 2662, 2669,
      2672, 2687, 2696, 2706, 2733, 2770, 2847, 2850, 2855, 2865, 2872, 2899, 2909, 2936, 2946,
      3007, 3112, 3139, 3474, 3484, 3556, 3659, 3660, 3661, 3664, 3667, 3668, 3674, 3687, 3712,
      3714, 3721, 3725, 3752, 3759, 3868, 3871, 3924, 4380, 4382, 4383, 4385, 4395, 4396, 4399,
      4409, 4432, 4433, 4435, 4445, 4470, 4472, 4473, 4480
    ] := by nativeDecideFin!
