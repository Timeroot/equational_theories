import equational_theories.Definability.Prn_prn8h4a
import equational_theories.Definability.Prn_prn8h4a_L4405
import equational_theories.Definability.FiniteFlavour

/-! Reuse the existing eight-point Klein-four exhaustive exclusion of E4405
for any source admitting the same automorphisms. No new search is required. -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace Magma.KleinFourEight

/-- No operation satisfying E4405 is definable in a source admitting this
Klein-four action, since every definable operation would preserve the action. -/
theorem not_definable (M : Magma (Fin 8))
    (hM : ∀ i, M.IsEndo (prn8h4a.E i)) : ¬ Law4405.DefinableOnMagma M := by
  rintro ⟨M', hM', hd⟩
  have hE : ∀ i, M'.IsEndo (prn8h4a.E i) := fun i ↦
    Magma.IsEndo.of_definable
      (e := ⟨prn8h4a.E i, prn8h4a.Einv i, prn8h4a.hl i, prn8h4a.hr i⟩) hd (hM i)
  have hop : M'.op = Magma.transport prn8h4a.E prn8h4a.tr
      (fun i ↦ M'.op (prn8h4a.rep i).1 (prn8h4a.rep i).2) :=
    Magma.op_eq_transport (rep := prn8h4a.rep) hE prn8h4a.htr
  have hok : ∀ (i : Fin 16) (x : Fin 8),
      Magma.orbitOK prn8h4a.E prn8h4a.z prn8h4a.st i x := by decide
  refine Magma.go_sound ordprn8h4a_Law4405.length ordprn8h4a_Law4405 le_rfl
    _ envprn8h4a_Law4405 noprn8h4a_Law4405
    (fun i ↦ M'.op (prn8h4a.rep i).1 (prn8h4a.rep i).2) ?_
    (fun i _ ↦ hok i _) ?_
  · intro x y hlt
    have hn : (Array.replicate (8 * 8) 8).getD (x.val * 8 + y.val) 8 = 8 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    omega
  · show @satisfies _ (Fin 8) (Magma.mk (Magma.transport prn8h4a.E prn8h4a.tr
      fun i ↦ M'.op (prn8h4a.rep i).1 (prn8h4a.rep i).2)) Law4405
    rw [← hop]
    exact hM'


end Magma.KleinFourEight
