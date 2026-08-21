import equational_theories.Definability.Aut_aut9h27a_data

/-! # No group of order 27 on Fin 9 invariant operation satisfies equation 1113 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut9h27a-invariant operation on `Fin 9` satisfies equation 1113. -/
theorem noaut9h27a_Law1113 : ∀ v : ∀ i : Fin 5,
    {x : Fin 9 // Magma.orbitOK aut9h27a.E aut9h27a.z aut9h27a.st i x},
    ¬ @satisfies _ (Fin 9)
      (Magma.mk (Magma.transport aut9h27a.E aut9h27a.tr fun i ↦ (v i).1)) Law1113 := by
  simp only [Law1113.models_iff]
  native_decide
