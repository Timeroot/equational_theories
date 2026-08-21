import equational_theories.Definability.Aut_aff31h930a_data

/-! # No group of order 930 on Fin 31 invariant operation satisfies equation 1489 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aff31h930a-invariant operation on `Fin 31` satisfies equation 1489. -/
theorem noaff31h930a_Law1489 : ∀ v : ∀ i : Fin 2,
    {x : Fin 31 // Magma.orbitOK aff31h930a.E aff31h930a.z aff31h930a.st i x},
    ¬ @satisfies _ (Fin 31)
      (Magma.mk (Magma.transport aff31h930a.E aff31h930a.tr fun i ↦ (v i).1)) Law1489 := by
  simp only [Law1489.models_iff]
  native_decide
