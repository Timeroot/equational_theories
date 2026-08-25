import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 13 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `23` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `23` equations. -/
theorem exactC45_refutes_12 :
    FamilyRefutes Magma.exactC45 [
      3581, 3582, 3583, 3584, 3585, 3586, 3587, 3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596,
      3597, 3598, 3599, 3600, 3602, 3603, 3604, 3605
    ] := by nativeDecideFin!
