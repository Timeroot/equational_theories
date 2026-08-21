import equational_theories.Definability.Aut_mau11h110a_data

/-! # No group of order 110 on Fin 11 invariant operation satisfies equation 546 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No mau11h110a-invariant operation on `Fin 11` satisfies equation 546. -/
theorem nomau11h110a_Law546 : ∀ v : ∀ i : Fin 2,
    {x : Fin 11 // Magma.orbitOK mau11h110a.E mau11h110a.z mau11h110a.st i x},
    ¬ @satisfies _ (Fin 11)
      (Magma.mk (Magma.transport mau11h110a.E mau11h110a.tr fun i ↦ (v i).1)) Law546 := by
  simp only [Law546.models_iff]
  native_decide
