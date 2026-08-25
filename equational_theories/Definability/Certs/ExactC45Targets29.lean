import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 30 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `24` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `24` equations. -/
theorem exactC45_refutes_29 :
    FamilyRefutes Magma.exactC45 [
      3950, 3953, 3956, 3957, 3959, 3960, 3963, 3966, 3967, 3969, 3970, 3971, 3974, 3975, 3977,
      3978, 3981, 3982, 3983, 3985, 3986, 3987, 3988, 3990
    ] := by nativeDecideFin!
