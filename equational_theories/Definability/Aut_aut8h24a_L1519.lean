import equational_theories.Definability.Aut_aut8h24a_data

/-! # No group of order 24 on Fin 8 invariant operation satisfies equation 1519 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut8h24a-invariant operation on `Fin 8` satisfies equation 1519. -/
theorem noaut8h24a_Law1519 : ∀ v : ∀ i : Fin 8,
    {x : Fin 8 // Magma.orbitOK aut8h24a.E aut8h24a.z aut8h24a.st i x},
    ¬ @satisfies _ (Fin 8)
      (Magma.mk (Magma.transport aut8h24a.E aut8h24a.tr fun i ↦ (v i).1)) Law1519 := by
  simp only [Law1519.models_iff]
  native_decide
