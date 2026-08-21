import equational_theories.Definability.Aut_aut9h24a_data

/-! # No group of order 24 on Fin 9 invariant operation satisfies equation 1479 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- No aut9h24a-invariant operation on `Fin 9` satisfies equation 1479. -/
theorem noaut9h24a_Law1479 : ∀ v : ∀ i : Fin 9,
    {x : Fin 9 // Magma.orbitOK aut9h24a.E aut9h24a.z aut9h24a.st i x},
    ¬ @satisfies _ (Fin 9)
      (Magma.mk (Magma.transport aut9h24a.E aut9h24a.tr fun i ↦ (v i).1)) Law1479 := by
  simp only [Law1479.models_iff]
  native_decide
