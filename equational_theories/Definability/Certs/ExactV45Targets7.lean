import equational_theories.Definability.ExactAut5V45

/-!
# Structural certificate targets: `Magma.exactV45` (part 8 of 9)

Equations with no model among the `14442` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEV45`. `371` of them are worth listing, of which `26` appear here;
each is a valid *target* `L` of a `Magma.exactV45` certificate, and so is not structural from any of
the `281` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `14442` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEV45` satisfies any of these `26` equations. -/
theorem exactV45_refutes_7 :
    FamilyRefutes Magma.exactV45 [
      4378, 4456, 4490, 4507, 4510, 4515, 4586, 4593, 4600, 4602, 4604, 4625, 4630, 4632, 4634,
      4638, 4649, 4654, 4655, 4657, 4663, 4669, 4672, 4674, 4675, 4676
    ] := by nativeDecideFin!
