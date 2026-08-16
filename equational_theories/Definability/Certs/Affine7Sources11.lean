import equational_theories.Definability.Certificates

/-!
# Definability certificate sources: `Magma.affine7` (part 12 of 12)

For each of the following magmas, drawn from the `7` magmas on `Fin 7` with all of `F₄₂ = AGL(1, 7)` as automorphisms, the equations in at most four variables
that it satisfies. Every one of the `2181` such equations with a model in the family appears
in at least one of these lists, so they are exactly the equations in at most four variables that
can be used as the *source* `L'` of a `Magma.affine7` certificate.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- `26` of the `126` equations satisfied by `Magma.affine7 6` (part 2 of 2). -/
theorem affine7_satisfies_6_1 :
    Satisfies (Magma.affine7 6) [
      3456, 3484, 3522, 3556, 3659, 3687, 3715, 3722, 3862, 3887, 3915, 3954, 3962, 4023, 4065,
      4074, 4081, 4118, 4157, 4275, 4307, 4380, 4409, 4435, 4470, 4658
    ] := by decide!
