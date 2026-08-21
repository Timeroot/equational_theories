import equational_theories.Definability.Aut_big59h1711a_data

/-! # No group of order 1711 on Fin 59 invariant operation satisfies equation 3472 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No big59h1711a-invariant operation on `Fin 59` satisfies equation 3472. -/
theorem nobig59h1711a_Law3472 : ∀ v : ∀ i : Fin 3,
    {x : Fin 59 // Magma.orbitOK big59h1711a.E big59h1711a.z big59h1711a.st i x},
    ¬ @satisfies _ (Fin 59)
      (Magma.mk (Magma.transport big59h1711a.E big59h1711a.tr fun i ↦ (v i).1)) Law3472 := by
  simp only [Law3472.models_iff]
  native_decide
