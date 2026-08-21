import equational_theories.Definability.Aut_aff17h272a_data

/-! # No group of order 272 on Fin 17 invariant operation satisfies equation 1113 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aff17h272a-invariant operation on `Fin 17` satisfies equation 1113. -/
theorem noaff17h272a_Law1113 : ∀ v : ∀ i : Fin 2,
    {x : Fin 17 // Magma.orbitOK aff17h272a.E aff17h272a.z aff17h272a.st i x},
    ¬ @satisfies _ (Fin 17)
      (Magma.mk (Magma.transport aff17h272a.E aff17h272a.tr fun i ↦ (v i).1)) Law1113 := by
  simp only [Law1113.models_iff]
  native_decide
