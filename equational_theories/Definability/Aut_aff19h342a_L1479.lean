import equational_theories.Definability.Aut_aff19h342a_data

/-! # No group of order 342 on Fin 19 invariant operation satisfies equation 1479 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aff19h342a-invariant operation on `Fin 19` satisfies equation 1479. -/
theorem noaff19h342a_Law1479 : ∀ v : ∀ i : Fin 2,
    {x : Fin 19 // Magma.orbitOK aff19h342a.E aff19h342a.z aff19h342a.st i x},
    ¬ @satisfies _ (Fin 19)
      (Magma.mk (Magma.transport aff19h342a.E aff19h342a.tr fun i ↦ (v i).1)) Law1479 := by
  simp only [Law1479.models_iff]
  native_decide
