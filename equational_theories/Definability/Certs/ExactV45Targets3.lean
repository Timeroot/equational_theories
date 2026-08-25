import equational_theories.Definability.ExactAut5V45

/-!
# Structural certificate targets: `Magma.exactV45` (part 4 of 9)

Equations with no model among the `14442` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEV45`. `371` of them are worth listing, of which `48` appear here;
each is a valid *target* `L` of a `Magma.exactV45` certificate, and so is not structural from any of
the `281` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `14442` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEV45` satisfies any of these `48` equations. -/
theorem exactV45_refutes_3 :
    FamilyRefutes Magma.exactV45 [
      3513, 3514, 3515, 3516, 3517, 3528, 3530, 3531, 3532, 3534, 3535, 3536, 3538, 3539, 3540,
      3541, 3542, 3543, 3544, 3545, 3558, 3566, 3588, 3669, 3702, 3716, 3726, 3727, 3751, 3758,
      3769, 3786, 3790, 3874, 3909, 3930, 3939, 3947, 3951, 3958, 3964, 3965, 3968, 3976, 3980,
      3984, 3993, 3994
    ] := by nativeDecideFin!
