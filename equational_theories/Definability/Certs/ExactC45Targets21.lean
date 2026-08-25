import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 22 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `21` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `21` equations. -/
theorem exactC45_refutes_21 :
    FamilyRefutes Magma.exactC45 [
      3784, 3785, 3787, 3788, 3789, 3791, 3792, 3793, 3795, 3796, 3797, 3798, 3799, 3800, 3801,
      3802, 3804, 3805, 3806, 3807, 3808
    ] := by nativeDecideFin!
