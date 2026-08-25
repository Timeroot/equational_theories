import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 49 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `28` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `28` equations. -/
theorem exactC45_refutes_48 :
    FamilyRefutes Magma.exactC45 [
      4384, 4387, 4391, 4394, 4400, 4402, 4404, 4407, 4411, 4414, 4416, 4418, 4419, 4422, 4427,
      4428, 4431, 4437, 4439, 4441, 4444, 4448, 4451, 4453, 4455, 4459, 4464, 4465
    ] := by nativeDecideFin!
