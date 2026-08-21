import equational_theories.Definability.Aut_aut9h72a_data

/-! # No group of order 72 on Fin 9 invariant operation satisfies equation 4408 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut9h72a-invariant operation on `Fin 9` satisfies equation 4408. -/
theorem noaut9h72a_Law4408 : ∀ v : ∀ i : Fin 2,
    {x : Fin 9 // Magma.orbitOK aut9h72a.E aut9h72a.z aut9h72a.st i x},
    ¬ @satisfies _ (Fin 9)
      (Magma.mk (Magma.transport aut9h72a.E aut9h72a.tr fun i ↦ (v i).1)) Law4408 := by
  simp only [Law4408.models_iff]
  native_decide
