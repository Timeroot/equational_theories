import equational_theories.Definability.ExactAut7D147

/-!
# Structural certificate targets: `Magma.exactD147` (part 1 of 1)

Equations with no model among the `336` magmas on `Fin 7` whose automorphism group is exactly the
order-`14` group of `Magma.permED147`. `48` of them are worth listing, of which `48` appear here;
each is a valid *target* `L` of a `Magma.exactD147` certificate, and so is not structural from any
of the `44` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut7`.
-/

set_option maxHeartbeats 1000000

/-- None of the `336` magmas on `Fin 7` whose automorphism group is exactly the order-`14` group of
`Magma.permED147` satisfies any of these `48` equations. -/
theorem exactD147_refutes_0 :
    FamilyRefutes Magma.exactD147 [
      58, 266, 437, 442, 640, 649, 653, 657, 669, 848, 860, 1237, 1437, 1457, 1481, 2051, 2070,
      2078, 2415, 2675, 2687, 2858, 2863, 2878, 2886, 2912, 3093, 3115, 3264, 3315, 3521, 3529,
      3549, 3556, 3728, 3732, 3917, 3924, 3931, 3952, 4076, 4165, 4314, 4358, 4398, 4442, 4606,
      4677
    ] := by nativeDecideFin!
