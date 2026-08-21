import equational_theories.Definability.Aut_aut9h18a_data

/-! # No group of order 18 on Fin 9 invariant operation satisfies equation 707 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut9h18a-invariant operation on `Fin 9` satisfies equation 707. -/
theorem noaut9h18a_Law707 : ∀ v : ∀ i : Fin 5,
    {x : Fin 9 // Magma.orbitOK aut9h18a.E aut9h18a.z aut9h18a.st i x},
    ¬ @satisfies _ (Fin 9)
      (Magma.mk (Magma.transport aut9h18a.E aut9h18a.tr fun i ↦ (v i).1)) Law707 := by
  simp only [Law707.models_iff]
  native_decide
