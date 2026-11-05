import equational_theories.Equations.All
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

/-!
A countable completion construction for E882, discovered by extending the
repository's greedy partial-table search. The four invariants are functionality,
the partially evaluated E882 law, and two small collision constraints.

To fill an undefined `a*b`, choose a fresh `c`, prescribe `a*b = c`, and also
prescribe `x*c = z` whenever `z*x = a` and `x*z = b` were already defined.
The extension preserves all four invariants, as checked directly by Lean below.
Enumerating pairs of natural numbers gives a total E882 operation containing
any finite starting table satisfying the invariants. No external certificate
or trusted computation is used.
-/
namespace Eq882

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X0 X3 ∨ ¬ R X2 X3 X4 ∨ R X1 X4 X0)
  rule_2 : (∀ X0 X1 X2, ¬ R X0 X1 X2 ∨ ¬ R X1 X0 X2 ∨ ¬ R X1 X1 X2 ∨ X0 = X1)
  rule_3 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X1 X0 X3 ∨ ¬ R X1 X4 X3 ∨ ¬ R X4 X1 X2 ∨ X0 = X4)
  finsupp : Finset G
  mem_1 : ∀ X Y Z, ¬R X Y Z ∨ X ∈ finsupp
  mem_2 : ∀ X Y Z, ¬R X Y Z ∨ Y ∈ finsupp
  mem_3 : ∀ X Y Z, ¬R X Y Z ∨ Z ∈ finsupp

variable {G : Type*} (ps : PartialSolution G)

set_option maxHeartbeats 2000000 in
/-- Fill an undefined product `a*b` with a fresh element `c`, and add exactly
those products `x*c = z` forced by existing pairs `z*x = a`, `x*z = b`. -/
theorem PartialSolution.adjoin (a b c : G) (ac : a ≠ c) (bc : c ≠ b)
    (p3 : ∀ z, ¬ ps.R a b z) (p4XY : ∀ x y, ¬ ps.R x y c)
    (p4XZ : ∀ x z, ¬ ps.R x c z) (p4YZ : ∀ y z, ¬ ps.R c y z) :
    ∃ next : PartialSolution G, next.R a b c ∧ ∀ x y z, ps.R x y z → next.R x y z := by
  classical
  let new (x y z : G) := ps.R x y z ∨
    (x = a ∧ y = b ∧ z = c) ∨ (y = c ∧ ps.R z x a ∧ ps.R x z b)
  have h0 := ps.rule_0
  have h1 := ps.rule_1
  have h2 := ps.rule_2
  have h3 := ps.rule_3
  refine ⟨{ R := new, rule_0 := ?_, rule_1 := ?_, rule_2 := ?_, rule_3 := ?_,
            finsupp := ps.finsupp ∪ {a, b, c}, mem_1 := ?_, mem_2 := ?_, mem_3 := ?_ }, ?_⟩
  · clear h1 h2
    grind only
  · intro x y z u v
    simp only [← imp_iff_not_or]
    intro hx hy hz
    rcases hx with hx | hx | hx <;>
      rcases hy with hy | hy | hy <;>
      rcases hz with hz | hz | hz <;> grind only
  · clear h1
    grind only
  · clear h1
    intro x y z u v
    simp only [← imp_iff_not_or]
    intro hx hy hz hw
    rcases hx with hx | hx | hx <;>
      rcases hy with hy | hy | hy <;>
      rcases hz with hz | hz | hz <;>
      rcases hw with hw | hw | hw <;> grind only
  · have hm := ps.mem_1
    clear h0 h1 h2 h3
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    grind only
  · have hm := ps.mem_2
    clear h0 h1 h2 h3
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    grind only
  · have hm := ps.mem_2
    have hm3 := ps.mem_3
    clear h0 h1 h2 h3
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    grind only
  · exact ⟨Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), fun _ _ _ h => Or.inl h⟩

open scoped Classical in
noncomputable def PartialSolution.addArbitrary [Infinite G] (a b : G) : PartialSolution G :=
  if h : ∃ c, ps.R a b c then ps else
    let c := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose
    have hc : c ∉ _ := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose_spec
    (ps.adjoin a b c (by simp_all [eq_comm]) (by simp_all)
        (by simpa using h) (fun _ _ h ↦ by have := (ps.mem_3 _ _ _).neg_resolve_left h; simp_all)
        (fun _ _ h ↦ by have := (ps.mem_2 _ _ _).neg_resolve_left h; simp_all)
        (fun _ _ h ↦ by have := (ps.mem_1 _ _ _).neg_resolve_left h; simp_all)).choose

lemma PartialSolution.addArbitrary_covers [Infinite G] (a b : G) :
    ∃ c, (ps.addArbitrary a b).R a b c := by
  unfold addArbitrary
  split
  · assumption
  · generalize_proofs h1 h2 h3
    exact ⟨h1.choose, (h3 h2).choose_spec.1⟩

lemma PartialSolution.addArbitrary_contains [Infinite G] (a b : G) :
    ∀ x y z, ps.R x y z → (ps.addArbitrary a b).R x y z := by
  unfold addArbitrary
  split
  · simp
  · generalize_proofs v1 v2 v3
    exact (v3 v2).choose_spec.2

variable (ps : PartialSolution ℕ)

include ps in
noncomputable def PartialSolution.complSeq : ℕ → PartialSolution ℕ
| 0 => ps
| n+1 => (complSeq n).addArbitrary n.unpair.1 n.unpair.2

lemma PartialSolution.complSeq_exists (a b : ℕ) : ∃ c, (complSeq ps (Nat.pair a b + 1)).R a b c := by
  simp [complSeq]
  apply addArbitrary_covers

lemma PartialSolution.complSeq_mono_add_one (i : ℕ) (a b c : ℕ) (h : (complSeq ps i).R a b c) :
    (complSeq ps (i + 1)).R a b c := by
  simp [complSeq]
  apply addArbitrary_contains
  exact h

lemma PartialSolution.complSeq_mono (i j : ℕ) (hij : i ≤ j) (a b c : ℕ) (h : (complSeq ps i).R a b c) :
    (complSeq ps j).R a b c := by
  induction hij
  · exact h
  · apply ps.complSeq_mono_add_one
    assumption

lemma PartialSolution.complSeq_exists_of_lt (a b i : ℕ) (h : Nat.pair a b < i) :
    ∃ c, (complSeq ps i).R a b c := by
  obtain ⟨c, hc⟩ := ps.complSeq_exists a b
  use c
  apply complSeq_mono _ _ _ _ _ _ _ hc
  omega

noncomputable def PartialSolution.compl (a b c : ℕ) : Prop :=
  (ps.complSeq (Nat.pair a b + 1)).R a b c

theorem PartialSolution.compl_rule0 (a b c d : ℕ)
    (h : ps.compl a b c) (h2 : ps.compl a b d) : c = d := by
  unfold compl at *
  have := (ps.complSeq (Nat.pair a b + 1)).rule_0 a b c d
  simp_all

theorem PartialSolution.compl_exists (a b : ℕ) : ∃ c, ps.compl a b c :=
  complSeq_exists ..

lemma PartialSolution.complSeq_of_compl_of_lt (a b i : ℕ) (habi : Nat.pair a b < i)
    (c : ℕ) (h : ps.compl a b c) : (ps.complSeq i).R a b c :=
  PartialSolution.complSeq_mono _ _ _ (by omega) _ _ _ h

lemma PartialSolution.complSeq_iff_of_lt (a b i : ℕ) (habi : Nat.pair a b < i)
    (c : ℕ) : ps.compl a b c ↔ (ps.complSeq i).R a b c := by
  constructor
  · intro
    apply PartialSolution.complSeq_of_compl_of_lt <;> assumption
  · intro h
    have ⟨c', hc⟩ := ps.compl_exists a b
    convert hc
    have := ps.complSeq_of_compl_of_lt a b i habi c' hc
    have := (ps.complSeq i).rule_0 a b c c'
    simp_all

theorem PartialSolution.compl_rule1 (X0 X1 X2 X3 X4 : ℕ) :
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X1 X0 X3 ∨ ¬ ps.compl X2 X3 X4 ∨ ps.compl X1 X4 X0 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X1 X0) (max (Nat.pair X2 X3) (max (Nat.pair X1 X4) 0)))
  repeat rw [PartialSolution.complSeq_iff_of_lt _ _ _ i]
  apply PartialSolution.rule_1
  all_goals omega

noncomputable def PartialSolution.complFun (a b : ℕ) : ℕ := (ps.compl_exists a b).choose

theorem PartialSolution.complFun_eq_iff (a b c : ℕ) : ps.complFun a b = c ↔ ps.compl a b c := by
  constructor
  · rintro rfl
    exact (ps.compl_exists a b).choose_spec
  · intro h
    have : ps.compl a b (ps.complFun a b) := (ps.compl_exists a b).choose_spec
    exact ps.compl_rule0 a b _ _ this h

lemma PartialSolution.of_R (a b c : ℕ) (h : ps.R a b c) : ps.complFun a b = c := by
  rw [PartialSolution.complFun_eq_iff]
  apply PartialSolution.complSeq_mono _ 0 _ (by simp) _ _ _ h

@[implicit_reducible] noncomputable def PartialSolution.toMagma : Magma ℕ where
  op := ps.complFun

theorem PartialSolution.toMagma_equation882 :
    letI := ps.toMagma
    Equation882 ℕ := by
  simp only [Equation882]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X0 X1 (ps.complFun X0 X1) (ps.complFun X1 X0) (ps.complFun (ps.complFun X0 X1) (ps.complFun X1 X0))

end Eq882