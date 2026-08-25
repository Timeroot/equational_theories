import equational_theories.Definability.ExactAut6S56

/-!
# Structural certificate targets: `Magma.exactS56` (part 1 of 1)

Equations with no model among the `22` magmas on `Fin 6` whose automorphism group is exactly the
order-`120` group of `Magma.permES56`. `41` of them are worth listing, of which `41` appear here;
each is a valid *target* `L` of a `Magma.exactS56` certificate, and so is not structural from any of
the `1202` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `22` magmas on `Fin 6` whose automorphism group is exactly the order-`120` group of
`Magma.permES56` satisfies any of these `41` equations. -/
theorem exactS56_refutes_0 :
    FamilyRefutes Magma.exactS56 [
      53, 72, 127, 160, 179, 212, 258, 273, 473, 562, 669, 879, 882, 909, 916, 1171, 1285, 1340,
      1374, 1432, 1467, 1470, 1525, 1670, 1793, 1876, 1983, 2044, 2097, 2186, 2199, 2244, 2271,
      2279, 2482, 2650, 2653, 2663, 2863, 3056, 3091
    ] := by nativeDecideFin!
