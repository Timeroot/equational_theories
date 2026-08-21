import equational_theories.Definability.Aut_mau9h54a_data

/-! # No group of order 54 on Fin 9 invariant operation satisfies equation 1719 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No mau9h54a-invariant operation on `Fin 9` satisfies equation 1719. -/
theorem nomau9h54a_Law1719 : ∀ v : ∀ i : Fin 3,
    {x : Fin 9 // Magma.orbitOK mau9h54a.E mau9h54a.z mau9h54a.st i x},
    ¬ @satisfies _ (Fin 9)
      (Magma.mk (Magma.transport mau9h54a.E mau9h54a.tr fun i ↦ (v i).1)) Law1719 := by
  simp only [Law1719.models_iff]
  native_decide
