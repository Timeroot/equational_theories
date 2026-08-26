import equational_theories.Definability.ExactEnd4N

/-!
# Term-structural certificate targets: `Magma.end4N`

Equations with no model among the `194` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`7` monoid of `Magma.endE4N`. `38` of them are worth listing, of which `38` appear here; each
is a valid *target* `L` of a `Magma.end4N` certificate, and so is not term-structural from any of
the `16` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `194` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`7` monoid of
`Magma.endE4N` satisfies any of these `38` equations. -/
theorem end4N_refutes_0 :
    FamilyRefutes Magma.end4N [
      327, 395, 427, 437, 473, 679, 834, 872, 1039, 1046, 1655, 1897, 2506, 2533, 2660, 2702,
      2873, 3056, 3105, 3115, 3323, 3324, 3520, 3523, 3524, 3527, 3972, 3989, 4006, 4040, 4226,
      4243, 4315, 4339, 4357, 4615, 4645, 4689
    ] := by nativeDecideFin!
