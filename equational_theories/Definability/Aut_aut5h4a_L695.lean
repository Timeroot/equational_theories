import equational_theories.Definability.Aut_aut5h4a_data

/-! # No group of order 4 on Fin 5 invariant operation satisfies equation 695 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut5h4a-invariant operation on `Fin 5` satisfies equation 695. -/
theorem noaut5h4a_Law695 : ∀ v : ∀ i : Fin 7,
    {x : Fin 5 // Magma.orbitOK aut5h4a.E aut5h4a.z aut5h4a.st i x},
    ¬ @satisfies _ (Fin 5)
      (Magma.mk (Magma.transport aut5h4a.E aut5h4a.tr fun i ↦ (v i).1)) Law695 := by
  simp only [Law695.models_iff]
  native_decide
