import equational_theories.Definability.ExactAut5V45

/-!
# Structural certificate targets: `Magma.exactV45` (part 5 of 9)

Equations with no model among the `14442` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEV45`. `371` of them are worth listing, of which `36` appear here;
each is a valid *target* `L` of a `Magma.exactV45` certificate, and so is not structural from any of
the `281` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `14442` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEV45` satisfies any of these `36` equations. -/
theorem exactV45_refutes_4 :
    FamilyRefutes Magma.exactV45 [
      3997, 4001, 4010, 4014, 4018, 4027, 4031, 4035, 4045, 4050, 4055, 4060, 4077, 4079, 4086,
      4112, 4117, 4119, 4122, 4123, 4124, 4125, 4126, 4129, 4132, 4133, 4134, 4136, 4137, 4139,
      4140, 4141, 4142, 4144, 4145, 4147
    ] := by nativeDecideFin!
