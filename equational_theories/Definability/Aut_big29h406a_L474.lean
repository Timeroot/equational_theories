import equational_theories.Definability.Aut_big29h406a_data

/-! # No group of order 406 on Fin 29 invariant operation satisfies equation 474 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No big29h406a-invariant operation on `Fin 29` satisfies equation 474. -/
theorem nobig29h406a_Law474 : ∀ v : ∀ i : Fin 3,
    {x : Fin 29 // Magma.orbitOK big29h406a.E big29h406a.z big29h406a.st i x},
    ¬ @satisfies _ (Fin 29)
      (Magma.mk (Magma.transport big29h406a.E big29h406a.tr fun i ↦ (v i).1)) Law474 := by
  simp only [Law474.models_iff]
  native_decide
