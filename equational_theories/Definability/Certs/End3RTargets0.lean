import equational_theories.Definability.ExactEnd3R

/-!
# Term-structural certificate targets: `Magma.end3R`

Equations with no model among the `15` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`5` monoid of `Magma.endE3R`. `40` of them are worth listing, of which `40` appear here; each
is a valid *target* `L` of a `Magma.end3R` certificate, and so is not term-structural from any of
the `71` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`5` monoid of
`Magma.endE3R` satisfies any of these `40` equations. -/
theorem end3R_refutes_0 :
    FamilyRefutes Magma.end3R [
      430, 630, 716, 843, 919, 1278, 1387, 1442, 1444, 1459, 1481, 1528, 1721, 1851, 2051, 2053,
      2064, 2090, 2152, 2254, 2282, 2673, 2709, 2876, 2902, 3142, 3259, 3281, 3308, 3323, 3474,
      3511, 3549, 3868, 3917, 3955, 4074, 4083, 4158, 4226
    ] := by nativeDecideFin!
