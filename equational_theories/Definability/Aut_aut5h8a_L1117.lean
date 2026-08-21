import equational_theories.Definability.Aut_aut5h8a

/-! # No group of order 8 on Fin 5 invariant operation satisfies equation 1117 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut5h8a-invariant operation on `Fin 5` satisfies equation 1117. -/
theorem noaut5h8a_Law1117 : ∀ v : ∀ i : Fin 6,
    {x : Fin 5 // Magma.orbitOK aut5h8a.E aut5h8a.z aut5h8a.st i x},
    ¬ @satisfies _ (Fin 5)
      (Magma.mk (Magma.transport aut5h8a.E aut5h8a.tr fun i ↦ (v i).1)) Law1117 := by
  simp only [Law1117.models_iff]
  native_decide
