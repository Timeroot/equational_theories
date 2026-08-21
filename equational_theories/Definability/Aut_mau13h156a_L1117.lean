import equational_theories.Definability.Aut_mau13h156a_data

/-! # No group of order 156 on Fin 13 invariant operation satisfies equation 1117 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No mau13h156a-invariant operation on `Fin 13` satisfies equation 1117. -/
theorem nomau13h156a_Law1117 : ∀ v : ∀ i : Fin 2,
    {x : Fin 13 // Magma.orbitOK mau13h156a.E mau13h156a.z mau13h156a.st i x},
    ¬ @satisfies _ (Fin 13)
      (Magma.mk (Magma.transport mau13h156a.E mau13h156a.tr fun i ↦ (v i).1)) Law1117 := by
  simp only [Law1117.models_iff]
  native_decide
