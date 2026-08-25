import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 20 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `29` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `29` equations. -/
theorem exactC45_refutes_19 :
    FamilyRefutes Magma.exactC45 [
      3669, 3673, 3676, 3683, 3697, 3702, 3705, 3706, 3710, 3711, 3713, 3717, 3718, 3719, 3720,
      3727, 3730, 3731, 3733, 3734, 3735, 3736, 3738, 3739, 3740, 3741, 3742, 3743, 3744
    ] := by nativeDecideFin!
