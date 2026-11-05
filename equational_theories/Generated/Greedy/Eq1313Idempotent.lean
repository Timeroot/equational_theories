import equational_theories.Equations.All
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

/-! Idempotent countable completion for E1313. A partial operation contains every
 diagonal product and only finitely many other products. Filling an undefined
 product with a fresh element and its forced companions preserves the rules.
 All extension and completion proofs are checked by the kernel. -/
namespace Eq1313Idempotent

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  diagonal : ∀ x, R x x x
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3 X4, ¬ R X0 X1 X2 ∨ ¬ R X2 X1 X3 ∨ ¬ R X3 X0 X4 ∨ R X0 X4 X1)
  rule_2 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X3 X1 X0 ∨ ¬ R X3 X2 X2 ∨ X2 = X1)
  rule_3 : (∀ X0 X1 X2 X3 X4 X5, ¬ R X0 X1 X2 ∨ ¬ R X3 X4 X2 ∨ ¬ R X5 X1 X0 ∨ ¬ R X5 X4 X3 ∨ X1 = X4)
  finsupp : Finset G
  mem_1 : ∀ X Y Z, ¬ R X Y Z ∨ (X = Y ∧ Y = Z) ∨ X ∈ finsupp
  mem_2 : ∀ X Y Z, ¬ R X Y Z ∨ (X = Y ∧ Y = Z) ∨ Y ∈ finsupp
  mem_3 : ∀ X Y Z, ¬ R X Y Z ∨ (X = Y ∧ Y = Z) ∨ Z ∈ finsupp

variable {G : Type*} (ps : PartialSolution G)

set_option maxHeartbeats 4000000 in
/-- Extend the partial multiplication without altering any old product. -/
theorem PartialSolution.adjoin (a b c : G) (ab : a ≠ b) (ac : a ≠ c) (bc : c ≠ b)
    (p3 : ∀ z, ¬ ps.R a b z)
    (p4XY : ∀ x y, ps.R x y c → x = c ∧ y = c)
    (p4XZ : ∀ x z, ps.R x c z → x = c ∧ z = c)
    (p4YZ : ∀ y z, ps.R c y z → y = c ∧ z = c) :
    ∃ next : PartialSolution G, next.R a b c ∧ ∀ x y z, ps.R x y z → next.R x y z := by
  classical
  let new (X Y Z : G) := ps.R X Y Z ∨
    (a = X ∧ b = Y ∧ c = Z) ∨
    (∃ X2, b = X ∧ c = Y ∧ ps.R b Z X2 ∧ ps.R X2 Z a)
  have hd := ps.diagonal
  have hda := ps.diagonal a
  have hdb := ps.diagonal b
  have hdc := ps.diagonal c
  have h0 := ps.rule_0
  have h1 := ps.rule_1
  have h2 := ps.rule_2
  have h3 := ps.rule_3
  have hdiag (x y : G) (h : ps.R x x y) : x = y :=
    ((ps.rule_0 x x x y).resolve_left (not_not.mpr (ps.diagonal x))).resolve_left (not_not.mpr h)
  have hcycle (x y z : G) (h : ps.R x y z) (h' : ps.R z y x) : x = y := by
    have hh := ps.rule_2 z y x x
    have hh' := ps.diagonal x
    tauto
  refine ⟨{ R := new, diagonal := fun x => Or.inl (hd x), rule_0 := ?_, rule_1 := ?_, rule_2 := ?_, rule_3 := ?_,
            finsupp := ps.finsupp ∪ {a, b, c}, mem_1 := ?_, mem_2 := ?_, mem_3 := ?_ }, ?_⟩
  · clear h1 h2
    intro x0 x1 x2 x3
    have hdx0 := ps.diagonal x0
    have hdx1 := ps.diagonal x1
    have hdx2 := ps.diagonal x2
    have hdx3 := ps.diagonal x3
    simp only [← imp_iff_not_or]
    intro hc0 hc1
    rcases hc0 with hc0 | ⟨hc0_0, hc0_1, hc0_2⟩ | ⟨w0_0, hc0_0, hc0_1, hc0_2, hc0_3⟩ <;>
      rcases hc1 with hc1 | ⟨hc1_0, hc1_1, hc1_2⟩ | ⟨w1_0, hc1_0, hc1_1, hc1_2, hc1_3⟩ <;> subst_vars <;> grind (instances := 1000) only
  · clear h3
    intro x0 x1 x2 x3 x4
    have hdx0 := ps.diagonal x0
    have hdx1 := ps.diagonal x1
    have hdx2 := ps.diagonal x2
    have hdx3 := ps.diagonal x3
    have hdx4 := ps.diagonal x4
    simp only [← imp_iff_not_or]
    intro hc0 hc1 hc2
    rcases hc0 with hc0 | ⟨hc0_0, hc0_1, hc0_2⟩ | ⟨w0_0, hc0_0, hc0_1, hc0_2, hc0_3⟩ <;>
      rcases hc1 with hc1 | ⟨hc1_0, hc1_1, hc1_2⟩ | ⟨w1_0, hc1_0, hc1_1, hc1_2, hc1_3⟩ <;>
      rcases hc2 with hc2 | ⟨hc2_0, hc2_1, hc2_2⟩ | ⟨w2_0, hc2_0, hc2_1, hc2_2, hc2_3⟩ <;> subst_vars <;> grind (instances := 1000) only
  · clear h1 h3
    intro x0 x1 x2 x3
    have hdx0 := ps.diagonal x0
    have hdx1 := ps.diagonal x1
    have hdx2 := ps.diagonal x2
    have hdx3 := ps.diagonal x3
    simp only [← imp_iff_not_or]
    intro hc0 hc1 hc2
    rcases hc0 with hc0 | ⟨hc0_0, hc0_1, hc0_2⟩ | ⟨w0_0, hc0_0, hc0_1, hc0_2, hc0_3⟩ <;>
      rcases hc1 with hc1 | ⟨hc1_0, hc1_1, hc1_2⟩ | ⟨w1_0, hc1_0, hc1_1, hc1_2, hc1_3⟩ <;>
      rcases hc2 with hc2 | ⟨hc2_0, hc2_1, hc2_2⟩ | ⟨w2_0, hc2_0, hc2_1, hc2_2, hc2_3⟩ <;> subst_vars <;> grind (instances := 1000) only
  · clear h1 h2
    intro x0 x1 x2 x3 x4 x5
    have hdx0 := ps.diagonal x0
    have hdx1 := ps.diagonal x1
    have hdx2 := ps.diagonal x2
    have hdx3 := ps.diagonal x3
    have hdx4 := ps.diagonal x4
    have hdx5 := ps.diagonal x5
    simp only [← imp_iff_not_or]
    intro hc0 hc1 hc2 hc3
    rcases hc0 with hc0 | ⟨hc0_0, hc0_1, hc0_2⟩ | ⟨w0_0, hc0_0, hc0_1, hc0_2, hc0_3⟩ <;>
      rcases hc1 with hc1 | ⟨hc1_0, hc1_1, hc1_2⟩ | ⟨w1_0, hc1_0, hc1_1, hc1_2, hc1_3⟩ <;>
      rcases hc2 with hc2 | ⟨hc2_0, hc2_1, hc2_2⟩ | ⟨w2_0, hc2_0, hc2_1, hc2_2, hc2_3⟩ <;>
      rcases hc3 with hc3 | ⟨hc3_0, hc3_1, hc3_2⟩ | ⟨w3_0, hc3_0, hc3_1, hc3_2, hc3_3⟩ <;> subst_vars <;> grind (instances := 1000) only
  · have hm := ps.mem_1
    have hm2 := ps.mem_2
    have hm3 := ps.mem_3
    clear h0 h1 h2 h3 hd
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    grind only
  · have hm := ps.mem_1
    have hm2 := ps.mem_2
    have hm3 := ps.mem_3
    clear h0 h1 h2 h3 hd
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    grind only
  · have hm := ps.mem_1
    have hm2 := ps.mem_2
    have hm3 := ps.mem_3
    clear h0 h1 h2 h3 hd
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    grind only
  · exact ⟨Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), fun _ _ _ h => Or.inl h⟩

open scoped Classical in
noncomputable def PartialSolution.addArbitrary [Infinite G] (a b : G) : PartialSolution G :=
  if h : ∃ c, ps.R a b c then ps else
    let c := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose
    have hc : c ∉ _ := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose_spec
    (ps.adjoin a b c (by intro hab; subst b; exact h ⟨a, ps.diagonal a⟩)
        (by simp_all [eq_comm]) (by simp_all) (by simpa using h)
        (fun x y hr ↦ by have := ps.mem_3 x y c; simp_all)
        (fun x z hr ↦ by have := ps.mem_2 x c z; simp_all)
        (fun y z hr ↦ by have := ps.mem_1 c y z; simp_all)).choose

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

theorem PartialSolution.compl_rule1 : (∀ X0 X1 X2 X3 X4, ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X2 X1 X3 ∨ ¬ ps.compl X3 X0 X4 ∨ ps.compl X0 X4 X1) := by
  intro X0 X1 X2 X3 X4
  let i := 1 + (max (Nat.pair X0 X4) (max (Nat.pair X3 X0) (max (Nat.pair X2 X1) (max (Nat.pair X0 X1) 0))))
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

theorem PartialSolution.toMagma_equation1313 :
    letI := ps.toMagma
    Equation1313 ℕ := by
  simp only [Equation1313]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 (X1) (X0) (ps.complFun X1 X0) (ps.complFun (ps.complFun X1 X0) X0) (ps.complFun (ps.complFun (ps.complFun X1 X0) X0) X1)

theorem PartialSolution.toMagma_idempotent (x : ℕ) :
    ps.complFun x x = x := ps.of_R x x x (ps.diagonal x)

/-- A prescribed cancellation failure, with every diagonal product included. -/
def collisionSeed : PartialSolution ℕ where
  R x y z := (x = y ∧ y = z) ∨ (x = 0 ∧ (y = 1 ∨ y = 2) ∧ z = 3) ∨ (y = 0 ∧ (x = 1 ∨ x = 2) ∧ z = 3)
  diagonal x := Or.inl ⟨rfl, rfl⟩
  rule_0 := by simp only [← imp_iff_not_or]; grind
  rule_1 := by simp only [← imp_iff_not_or]; grind
  rule_2 := by simp only [← imp_iff_not_or]; grind
  rule_3 := by simp only [← imp_iff_not_or]; grind
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or, Finset.mem_insert, Finset.mem_singleton]; grind
  mem_2 := by simp only [← imp_iff_not_or, Finset.mem_insert, Finset.mem_singleton]; grind
  mem_3 := by simp only [← imp_iff_not_or, Finset.mem_insert, Finset.mem_singleton]; grind

end Eq1313Idempotent
