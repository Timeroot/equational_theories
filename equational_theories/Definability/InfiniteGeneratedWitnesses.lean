import equational_theories.Definability.UnaryRecoveryBounds
import equational_theories.ManuallyProved.Equation1076

/-! Infinite term-recovery obstructions from the existing E1076 greedy extension.
Its finite models are idempotent, so these witnesses distinguish the finite and
unrestricted questions. No new extension construction is needed here. -/

open Law Law.MagmaLaw RecoverySubmagmas
namespace InfiniteGeneratedWitnesses

theorem Equation3_not_termStructuralFrom_Equation1076 :
    ¬ Law3.TermStructuralFrom Law1076 := by
  obtain ⟨G, M, h1076, h3, _⟩ := Eq1076.refute_seed1
  have hx : ∃ x : G, M.op x x ≠ x := by
    by_contra! hn
    exact h3 (fun x => (hn x).symm)
  obtain ⟨x, hx⟩ := hx
  exact not_idempotent_recovery_all M ((@Law1076.models_iff G M).mpr h1076) x hx

/-- info: 'InfiniteGeneratedWitnesses.Equation3_not_termStructuralFrom_Equation1076' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3_not_termStructuralFrom_Equation1076

/-- The existing E1076 extension preserves `0*0=1` and `0*1=2`.
An E3715 companion generates at most two points from any singleton. -/
theorem Equation3715_not_termStructuralFrom_Equation1076 :
    ¬ Law3715.TermStructuralFrom Law1076 := by
  open Eq1076 Eq1076.Greedy PartialMagma in
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed1 :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  let M : Magma (GreedyMagma e) := inferInstance
  have r1 : M.op 0 0 = 1 := fromList_eval he 0 0 1
  have r2 : M.op 0 1 = 2 := fromList_eval he 0 1 2
  intro h
  obtain ⟨N, hN, _, hr⟩ := h M ((@Law1076.models_iff _ M).mpr e.eq1076)
  have hcN : Magma.GenerationOrder.Closed N.op ({0, N.op 0 0} : Set (GreedyMagma e)) := by
    convert UnaryRecoveryBounds.closed3715 N ((@Law3715.models_iff _ N).mp hN) 0 using 1
    ext z
    simp only [UnaryRecoveryBounds.basis3715, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  have hc := Magma.GenerationOrder.closed_of_termDefinable hr hcN
  have h0 : (0 : GreedyMagma e) ∈ ({0, N.op 0 0} : Set (GreedyMagma e)) := by simp
  have h1 : (1 : GreedyMagma e) ∈ ({0, N.op 0 0} : Set (GreedyMagma e)) := by
    rw [← r1]
    exact hc 0 h0 0 h0
  have h2 : (2 : GreedyMagma e) ∈ ({0, N.op 0 0} : Set (GreedyMagma e)) := by
    rw [← r2]
    exact hc 0 h0 1 h1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  change (1 : Nat) = 0 ∨ 1 = N.op 0 0 at h1
  change (2 : Nat) = 0 ∨ 2 = N.op 0 0 at h2
  have h1' : (1 : Nat) = N.op 0 0 := h1.resolve_left (by decide)
  have h2' : (2 : Nat) = N.op 0 0 := h2.resolve_left (by decide)
  exact (by decide : (1 : Nat) ≠ 2) (h1'.trans h2'.symm)

/-- info: 'InfiniteGeneratedWitnesses.Equation3715_not_termStructuralFrom_Equation1076' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3715_not_termStructuralFrom_Equation1076
end InfiniteGeneratedWitnesses
