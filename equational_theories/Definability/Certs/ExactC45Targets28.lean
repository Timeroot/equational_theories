import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 29 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `25` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `25` equations. -/
theorem exactC45_refutes_28 :
    FamilyRefutes Magma.exactC45 [
      3876, 3886, 3900, 3913, 3914, 3916, 3919, 3920, 3922, 3923, 3926, 3929, 3933, 3934, 3936,
      3937, 3938, 3940, 3941, 3942, 3944, 3945, 3946, 3948, 3949
    ] := by nativeDecideFin!
