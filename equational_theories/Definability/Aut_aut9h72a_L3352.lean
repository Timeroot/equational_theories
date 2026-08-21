import equational_theories.Definability.Aut_aut9h72a_data

/-! # No group of order 72 on Fin 9 invariant operation satisfies equation 3352 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut9h72a-invariant operation on `Fin 9` satisfies equation 3352. -/
theorem noaut9h72a_Law3352 : ∀ v : ∀ i : Fin 2,
    {x : Fin 9 // Magma.orbitOK aut9h72a.E aut9h72a.z aut9h72a.st i x},
    ¬ @satisfies _ (Fin 9)
      (Magma.mk (Magma.transport aut9h72a.E aut9h72a.tr fun i ↦ (v i).1)) Law3352 := by
  simp only [Law3352.models_iff]
  native_decide
