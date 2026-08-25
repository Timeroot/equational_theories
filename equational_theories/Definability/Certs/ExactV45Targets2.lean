import equational_theories.Definability.ExactAut5V45

/-!
# Structural certificate targets: `Magma.exactV45` (part 3 of 9)

Equations with no model among the `14442` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEV45`. `371` of them are worth listing, of which `29` appear here;
each is a valid *target* `L` of a `Magma.exactV45` certificate, and so is not structural from any of
the `281` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `14442` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEV45` satisfies any of these `29` equations. -/
theorem exactV45_refutes_2 :
    FamilyRefutes Magma.exactV45 [
      3341, 3342, 3349, 3352, 3356, 3359, 3363, 3367, 3371, 3375, 3380, 3384, 3392, 3397, 3401,
      3405, 3409, 3418, 3422, 3426, 3431, 3436, 3441, 3446, 3451, 3470, 3495, 3508, 3510
    ] := by nativeDecideFin!
