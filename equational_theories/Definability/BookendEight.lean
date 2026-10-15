import equational_theories.Definability.KleinFourEight

/-!
# Eight-point first-order separation of E167 from E4405

The source admits the Klein four group on two regular orbits. The existing
`prn8h4a` search already excludes every E4405 operation invariant under this
action. Only a new source table is required; its law and symmetries are
checked by kernel reduction. No new exhaustive search is replayed here.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace Magma.BookendEight

/-- An idempotent E167 model in the numbering of `prn8h4a`. -/
def table : Array (Array Nat) := #[
  #[0, 3, 1, 3, 7, 6, 3, 5],
  #[2, 1, 2, 0, 7, 6, 4, 2],
  #[2, 0, 2, 0, 7, 0, 0, 0],
  #[1, 3, 1, 3, 1, 6, 1, 1],
  #[2, 3, 1, 6, 4, 6, 6, 5],
  #[2, 3, 7, 0, 7, 5, 4, 7],
  #[5, 3, 5, 5, 5, 6, 6, 5],
  #[2, 4, 4, 4, 7, 4, 4, 7]]

@[reducible]
def model : Magma (Fin 8) := ⟨fun x y ↦
  ⟨(table[x.val]!)[y.val]! % 8, Nat.mod_lt _ (by decide)⟩⟩

theorem models : @satisfies _ (Fin 8) model Law167 :=
  (@Law167.models_iff (Fin 8) model).mpr (by decide)

theorem endo : ∀ i, model.IsEndo (prn8h4a.E i) := by decide

/-- No E4405 operation can be defined in the displayed finite source. -/
theorem not_definable : ¬ Law4405.DefinableOnMagma model :=
  KleinFourEight.not_definable model endo

end Magma.BookendEight

theorem Equation4405_not_definableFromFin_Equation167 :
    ¬ Law4405.DefinableFromFin Law167 :=
  fun h ↦ Magma.BookendEight.not_definable (h _ Magma.BookendEight.models)

theorem Equation4405_not_definableFrom_Equation167 :
    ¬ Law4405.DefinableFrom Law167 :=
  fun h ↦ Equation4405_not_definableFromFin_Equation167 (definableFin_of_definable h)
