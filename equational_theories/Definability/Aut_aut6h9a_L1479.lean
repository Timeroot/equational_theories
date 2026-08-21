import equational_theories.Definability.Aut_aut6h9a

/-! # No group of order 9 on Fin 6 invariant operation satisfies equation 1479 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut6h9a-invariant operation on `Fin 6` satisfies equation 1479. -/
theorem noaut6h9a_Law1479 : ∀ v : ∀ i : Fin 8,
    {x : Fin 6 // Magma.orbitOK aut6h9a.E aut6h9a.z aut6h9a.st i x},
    ¬ @satisfies _ (Fin 6)
      (Magma.mk (Magma.transport aut6h9a.E aut6h9a.tr fun i ↦ (v i).1)) Law1479 := by
  simp only [Law1479.models_iff]
  native_decide
