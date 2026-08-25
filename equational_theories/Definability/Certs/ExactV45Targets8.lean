import equational_theories.Definability.ExactAut5V45

/-!
# Structural certificate targets: `Magma.exactV45` (part 9 of 9)

Equations with no model among the `14442` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEV45`. `371` of them are worth listing, of which `2` appear here; each
is a valid *target* `L` of a `Magma.exactV45` certificate, and so is not structural from any of the
`281` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `14442` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEV45` satisfies any of these `2` equations. -/
theorem exactV45_refutes_8 :
    FamilyRefutes Magma.exactV45 [
      4682, 4693
    ] := by nativeDecideFin!
