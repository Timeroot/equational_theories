import equational_theories.Definability.Aut_aut6h6c

/-! # No group of order 6 on Fin 6 (#3) invariant operation satisfies equation 4408 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut6h6c-invariant operation on `Fin 6` satisfies equation 4408. -/
theorem noaut6h6c_Law4408 : ∀ v : ∀ i : Fin 6,
    {x : Fin 6 // Magma.orbitOK aut6h6c.E aut6h6c.z aut6h6c.st i x},
    ¬ @satisfies _ (Fin 6)
      (Magma.mk (Magma.transport aut6h6c.E aut6h6c.tr fun i ↦ (v i).1)) Law4408 := by
  simp only [Law4408.models_iff]
  native_decide
