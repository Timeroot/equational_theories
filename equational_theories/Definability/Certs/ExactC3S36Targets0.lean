import equational_theories.Definability.ExactAut6C3S36

/-!
# Structural certificate targets: `Magma.exactC3S36` (part 1 of 1)

Equations with no model among the `156` magmas on `Fin 6` whose automorphism group is exactly the
order-`18` group of `Magma.permEC3S36`. `28` of them are worth listing, of which `28` appear here;
each is a valid *target* `L` of a `Magma.exactC3S36` certificate, and so is not structural from any
of the `49` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `156` magmas on `Fin 6` whose automorphism group is exactly the order-`18` group of
`Magma.permEC3S36` satisfies any of these `28` equations. -/
theorem exactC3S36_refutes_0 :
    FamilyRefutes Magma.exactC3S36 [
      127, 160, 179, 212, 315, 362, 473, 1085, 1278, 1655, 1657, 1721, 1851, 1860, 2254, 3271,
      3388, 3474, 3495, 3667, 3668, 3687, 3868, 3874, 4071, 4143, 4403, 4420
    ] := by nativeDecideFin!
