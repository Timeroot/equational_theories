import equational_theories.Definability.Aut_mau9h72a_data

/-! # No group of order 72 on Fin 9 invariant operation satisfies equation 1117 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No mau9h72a-invariant operation on `Fin 9` satisfies equation 1117. -/
theorem nomau9h72a_Law1117 : ∀ v : ∀ i : Fin 2,
    {x : Fin 9 // Magma.orbitOK mau9h72a.E mau9h72a.z mau9h72a.st i x},
    ¬ @satisfies _ (Fin 9)
      (Magma.mk (Magma.transport mau9h72a.E mau9h72a.tr fun i ↦ (v i).1)) Law1117 := by
  simp only [Law1117.models_iff]
  native_decide
