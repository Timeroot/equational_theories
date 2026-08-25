import equational_theories.Definability.ExactEnd3Q

/-!
# Term-structural certificate targets: `Magma.end3Q`

Equations with no model among the `2` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`9` monoid of `Magma.endE3Q`. `55` of them are worth listing, of which `55` appear here; each
is a valid *target* `L` of a `Magma.end3Q` certificate, and so is not term-structural from any of
the `56` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`9` monoid of
`Magma.endE3Q` satisfies any of these `55` equations. -/
theorem end3Q_refutes_0 :
    FamilyRefutes Magma.end3Q [
      417, 466, 500, 513, 528, 575, 617, 620, 1075, 1226, 1325, 1442, 1455, 1632, 1635, 1684,
      1691, 1838, 1848, 1894, 1921, 2137, 2267, 2327, 2457, 2909, 2936, 3053, 3066, 3079, 3083,
      3094, 3112, 3259, 3334, 3353, 3459, 3462, 3511, 3518, 3526, 3880, 3887, 3955, 3962, 4023,
      4083, 4127, 4146, 4275, 4283, 4307, 4585, 4635, 4656
    ] := by nativeDecideFin!
