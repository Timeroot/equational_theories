import equational_theories.Definability.Aut_aut6h6a_data

/-! # No group of order 6 on Fin 6 invariant operation satisfies equation 335 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut6h6a-invariant operation on `Fin 6` satisfies equation 335. -/
theorem noaut6h6a_Law335 : ∀ v : ∀ i : Fin 8,
    {x : Fin 6 // Magma.orbitOK aut6h6a.E aut6h6a.z aut6h6a.st i x},
    ¬ @satisfies _ (Fin 6)
      (Magma.mk (Magma.transport aut6h6a.E aut6h6a.tr fun i ↦ (v i).1)) Law335 := by
  simp only [Law335.models_iff]
  native_decide
