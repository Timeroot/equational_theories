import equational_theories.Definability.KleinFourEight

/-!
# Eight-point first-order separation of E1483 from E4405

The source admits a free Klein-four action with two orbits. Every definable
operation preserves that action, while the existing `prn8h4a` exclusion rules
out all invariant E4405 operations. The existing E1485 source already has
these symmetries; only its E1483 law needs the new kernel check.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace Magma.Central1483Eight

/-- The existing E1485 witness also satisfies E1483. -/
abbrev model : Magma (Fin 8) := prn8h4aM1485

theorem models : @satisfies _ (Fin 8) model Law1483 :=
  (@Law1483.models_iff (Fin 8) model).mpr (by decide)

theorem endo : ∀ i, model.IsEndo (prn8h4a.E i) := prn8h4aM1485_endo

end Magma.Central1483Eight

theorem Equation4405_not_definableFromFin_Equation1483 :
    ¬ Law4405.DefinableFromFin Law1483 :=
  fun h ↦ Magma.KleinFourEight.not_definable _ Magma.Central1483Eight.endo
    (h _ Magma.Central1483Eight.models)

theorem Equation4405_not_definableFrom_Equation1483 :
    ¬ Law4405.DefinableFrom Law1483 :=
  fun h ↦ Equation4405_not_definableFromFin_Equation1483 (definableFin_of_definable h)
