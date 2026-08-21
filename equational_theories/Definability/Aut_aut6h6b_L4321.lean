import equational_theories.Definability.Aut_aut6h6b

/-! # No group of order 6 on Fin 6 (#2) invariant operation satisfies equation 4321 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut6h6b-invariant operation on `Fin 6` satisfies equation 4321. -/
theorem noaut6h6b_Law4321 : ∀ v : ∀ i : Fin 6,
    {x : Fin 6 // Magma.orbitOK aut6h6b.E aut6h6b.z aut6h6b.st i x},
    ¬ @satisfies _ (Fin 6)
      (Magma.mk (Magma.transport aut6h6b.E aut6h6b.tr fun i ↦ (v i).1)) Law4321 := by
  simp only [Law4321.models_iff]
  native_decide
