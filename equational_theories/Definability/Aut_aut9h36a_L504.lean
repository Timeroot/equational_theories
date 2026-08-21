import equational_theories.Definability.Aut_aut9h36a_data

/-! # No group of order 36 on Fin 9 invariant operation satisfies equation 504 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut9h36a-invariant operation on `Fin 9` satisfies equation 504. -/
theorem noaut9h36a_Law504 : ∀ v : ∀ i : Fin 3,
    {x : Fin 9 // Magma.orbitOK aut9h36a.E aut9h36a.z aut9h36a.st i x},
    ¬ @satisfies _ (Fin 9)
      (Magma.mk (Magma.transport aut9h36a.E aut9h36a.tr fun i ↦ (v i).1)) Law504 := by
  simp only [Law504.models_iff]
  native_decide
