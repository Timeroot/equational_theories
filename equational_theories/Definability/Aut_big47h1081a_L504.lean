import equational_theories.Definability.Aut_big47h1081a_data

/-! # No group of order 1081 on Fin 47 invariant operation satisfies equation 504 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No big47h1081a-invariant operation on `Fin 47` satisfies equation 504. -/
theorem nobig47h1081a_Law504 : ∀ v : ∀ i : Fin 3,
    {x : Fin 47 // Magma.orbitOK big47h1081a.E big47h1081a.z big47h1081a.st i x},
    ¬ @satisfies _ (Fin 47)
      (Magma.mk (Magma.transport big47h1081a.E big47h1081a.tr fun i ↦ (v i).1)) Law504 := by
  simp only [Law504.models_iff]
  native_decide
