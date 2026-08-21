import equational_theories.Definability.Aut_aff13h156a_data

/-! # No group of order 156 on Fin 13 invariant operation satisfies equation 870 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aff13h156a-invariant operation on `Fin 13` satisfies equation 870. -/
theorem noaff13h156a_Law870 : ∀ v : ∀ i : Fin 2,
    {x : Fin 13 // Magma.orbitOK aff13h156a.E aff13h156a.z aff13h156a.st i x},
    ¬ @satisfies _ (Fin 13)
      (Magma.mk (Magma.transport aff13h156a.E aff13h156a.tr fun i ↦ (v i).1)) Law870 := by
  simp only [Law870.models_iff]
  native_decide
