import equational_theories.Definability.ExactEnd5U

/-!
# Term-structural certificate targets: `Magma.end5U`

Equations with no model among the `22` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`15` monoid of `Magma.endE5U`. `53` of them are worth listing, of which `53` appear here; each
is a valid *target* `L` of a `Magma.end5U` certificate, and so is not term-structural from any of
the `21` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `22` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`15` monoid of
`Magma.endE5U` satisfies any of these `53` equations. -/
theorem end5U_refutes_0 :
    FamilyRefutes Magma.end5U [
      153, 156, 312, 323, 360, 378, 427, 1022, 1038, 1241, 1644, 1654, 1657, 1834, 1840, 1860,
      2256, 2456, 2459, 3105, 3268, 3288, 3309, 3471, 3474, 3481, 3484, 3511, 3518, 3663, 3665,
      3668, 3677, 3687, 3694, 3863, 3865, 3868, 3871, 3955, 3962, 4066, 4069, 4121, 4272, 4291,
      4351, 4381, 4470, 4483, 4583, 4597, 4629
    ] := by nativeDecideFin!
