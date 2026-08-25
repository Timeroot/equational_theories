import equational_theories.Definability.ExactAut5V45

/-!
# Structural certificate targets: `Magma.exactV45` (part 6 of 9)

Equations with no model among the `14442` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEV45`. `371` of them are worth listing, of which `26` appear here;
each is a valid *target* `L` of a `Magma.exactV45` certificate, and so is not structural from any of
the `281` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `14442` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEV45` satisfies any of these `26` equations. -/
theorem exactV45_refutes_5 :
    FamilyRefutes Magma.exactV45 [
      4148, 4149, 4150, 4151, 4152, 4153, 4161, 4164, 4167, 4168, 4171, 4179, 4183, 4187, 4196,
      4200, 4204, 4213, 4217, 4221, 4230, 4234, 4238, 4248, 4253, 4258
    ] := by nativeDecideFin!
