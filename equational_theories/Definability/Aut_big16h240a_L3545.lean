import equational_theories.Definability.Aut_big16h240a_data

/-! # No group of order 240 on Fin 16 invariant operation satisfies equation 3545 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No big16h240a-invariant operation on `Fin 16` satisfies equation 3545. -/
theorem nobig16h240a_Law3545 : ∀ v : ∀ i : Fin 2,
    {x : Fin 16 // Magma.orbitOK big16h240a.E big16h240a.z big16h240a.st i x},
    ¬ @satisfies _ (Fin 16)
      (Magma.mk (Magma.transport big16h240a.E big16h240a.tr fun i ↦ (v i).1)) Law3545 := by
  simp only [Law3545.models_iff]
  native_decide
