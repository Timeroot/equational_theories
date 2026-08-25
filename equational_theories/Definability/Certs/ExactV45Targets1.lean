import equational_theories.Definability.ExactAut5V45

/-!
# Structural certificate targets: `Magma.exactV45` (part 2 of 9)

Equations with no model among the `14442` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEV45`. `371` of them are worth listing, of which `61` appear here;
each is a valid *target* `L` of a `Magma.exactV45` certificate, and so is not structural from any of
the `281` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `14442` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEV45` satisfies any of these `61` equations. -/
theorem exactV45_refutes_1 :
    FamilyRefutes Magma.exactV45 [
      2373, 2376, 2447, 2536, 2541, 2602, 2656, 2660, 2666, 2688, 2697, 2702, 2710, 2712, 2725,
      2744, 2755, 2774, 2782, 2808, 2853, 2856, 2860, 2863, 2873, 2880, 2883, 2940, 2979, 2992,
      2998, 3069, 3076, 3180, 3195, 3260, 3267, 3292, 3300, 3305, 3307, 3310, 3311, 3312, 3313,
      3314, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3335, 3336, 3337, 3338, 3339,
      3340
    ] := by nativeDecideFin!
