import equational_theories.Definability.ExactAut7S4b7

/-!
# Structural certificate targets: `Magma.exactS4b7` (part 1 of 1)

Equations with no model among the `160` magmas on `Fin 7` whose automorphism group is exactly the
order-`24` group of `Magma.permES4b7`. `18` of them are worth listing, of which `18` appear here;
each is a valid *target* `L` of a `Magma.exactS4b7` certificate, and so is not structural from any
of the `31` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut7`.
-/

set_option maxHeartbeats 1000000

/-- None of the `160` magmas on `Fin 7` whose automorphism group is exactly the order-`24` group of
`Magma.permES4b7` satisfies any of these `18` equations. -/
theorem exactS4b7_refutes_0 :
    FamilyRefutes Magma.exactS4b7 [
      437, 1039, 1046, 1242, 1721, 1851, 2330, 2506, 2533, 3115, 3343, 4130, 4273, 4321, 4408,
      4479, 4588, 4636
    ] := by nativeDecideFin!
