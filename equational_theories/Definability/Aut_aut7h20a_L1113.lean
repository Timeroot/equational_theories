import equational_theories.Definability.Aut_aut7h20a_data

/-! # No group of order 20 on Fin 7 invariant operation satisfies equation 1113 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut7h20a-invariant operation on `Fin 7` satisfies equation 1113. -/
theorem noaut7h20a_Law1113 : ∀ v : ∀ i : Fin 10,
    {x : Fin 7 // Magma.orbitOK aut7h20a.E aut7h20a.z aut7h20a.st i x},
    ¬ @satisfies _ (Fin 7)
      (Magma.mk (Magma.transport aut7h20a.E aut7h20a.tr fun i ↦ (v i).1)) Law1113 := by
  simp only [Law1113.models_iff]
  native_decide
