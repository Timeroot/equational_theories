import equational_theories.Definability.Aut_aut6h6b

/-! # No group of order 6 on Fin 6 (#2) invariant operation satisfies equation 335 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut6h6b-invariant operation on `Fin 6` satisfies equation 335. -/
theorem noaut6h6b_Law335 : ∀ v : ∀ i : Fin 6,
    {x : Fin 6 // Magma.orbitOK aut6h6b.E aut6h6b.z aut6h6b.st i x},
    ¬ @satisfies _ (Fin 6)
      (Magma.mk (Magma.transport aut6h6b.E aut6h6b.tr fun i ↦ (v i).1)) Law335 := by
  simp only [Law335.models_iff]
  native_decide
