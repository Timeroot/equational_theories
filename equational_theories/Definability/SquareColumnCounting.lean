import equational_theories.Definability.EightRowCounting
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Counting magmas invariant under squaring the right input

For E326, fixing the diagonal fixes one entry per row. A nonidentity diagonal
also identifies two columns, leaving at most n-2 independent entries per row.
Thus there are at most twice as many E326 tables as idempotent tables. Combined
with the E8 count and compactness, this refutes E8 → E326 structurally on
arbitrary magmas.
-/

open Law Law.MagmaLaw
namespace SquareColumnCounting
variable {A : Type} [Fintype A] [DecidableEq A]
abbrev Row (s : A → A) (x : A) := {f : A → A // f x = s x ∧ ∀ y, f y = f (s y)}
abbrev Outside (x o : A) := {z : A // z ∉ ({x,o} : Finset A)}

theorem row_bound (s : A → A) (a : A) (ha : s a ≠ a) (x : A) :
    Fintype.card (Row s x) ≤ Fintype.card A ^ (Fintype.card A - 2) := by
  let o := if x = a then s a else a
  have hxo : x ≠ o := by
    dsimp [o]
    split_ifs with h
    · exact h ▸ ha.symm
    · exact h
  let enc : Row s x → (Outside x o → A) := fun f z => f.val z.val
  have inj : Function.Injective enc := by
    intro f g h
    apply Subtype.ext
    funext z
    have free (w : A) (hwx : w ≠ x) (hwo : w ≠ o) : f.val w = g.val w :=
      congrFun h ⟨w, by simp [hwx, hwo]⟩
    by_cases hz : z = x
    · subst z; exact f.property.1.trans g.property.1.symm
    by_cases hzo : z = o
    · subst z
      by_cases hxa : x = a
      · subst x
        simp only [o, if_pos rfl]
        exact (f.property.2 a).symm.trans (f.property.1.trans
          (g.property.1.symm.trans (g.property.2 a)))
      · have hoa : o = a := if_neg hxa
        rw [hoa, f.property.2 a, g.property.2 a]
        by_cases hax : s a = x
        · rw [hax, f.property.1, g.property.1]
        · exact free (s a) hax (by simpa [hoa] using ha)
    · exact free z hz hzo
  have hc : Fintype.card (Outside x o) = Fintype.card A - 2 := by
    have hh := Fintype.card_subtype_compl (fun z : A => z ∈ ({x,o} : Finset A))
    simpa only [Fintype.card_coe, Finset.card_pair hxo] using hh
  simpa only [Fintype.card_fun, hc] using Fintype.card_le_of_injective enc inj

def tableEncode :
    {f : A → A → A // @Equation326 A ⟨f⟩} → Σ s : A → A, (x : A) → Row s x :=
  fun f => ⟨fun x => f.val x x, fun x => ⟨f.val x, rfl, f.property x⟩⟩

omit [Fintype A] [DecidableEq A] in
theorem tableEncode_injective : Function.Injective (tableEncode (A := A)) := by
  intro f g h
  apply Subtype.ext
  exact congrArg (fun p : Σ s : A → A, (x : A) → Row s x =>
    fun x y => (p.2 x).val y) h


theorem fixed_bound (s : A → A) (hs : s ≠ id) :
    Fintype.card ((x : A) → Row s x) ≤
      (Fintype.card A ^ (Fintype.card A - 2)) ^ Fintype.card A := by
  obtain ⟨a,ha⟩ : ∃ a, s a ≠ a := by
    by_contra h
    push Not at h
    exact hs (funext h)
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _x : A, Fintype.card A ^ (Fintype.card A - 2) := by
      apply Finset.prod_le_prod
      · intro x _; exact Nat.zero_le _
      · intro x _; exact row_bound s a ha x
    _ = _ := by simp

noncomputable def idemRowEquiv (x : A) : Row id x ≃ EightRowCounting.Fiber x x where
  toFun f := ⟨f.val, f.property.1, f.property.1⟩
  invFun f := ⟨f.val, f.property.1, fun _ => rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem id_count : Fintype.card ((x : A) → Row id x) =
    (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_congr (idemRowEquiv _), EightRowCounting.card_fiber,
    EightRowCounting.card_self_pair, Finset.prod_const, Finset.card_univ]

theorem count_bound (hn : 2 ≤ Fintype.card A) :
    Fintype.card {f : A → A → A // @Equation326 A ⟨f⟩} ≤
      2 * (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  let n := Fintype.card A
  let I := (n ^ (n - 1)) ^ n
  let J := (n ^ (n - 2)) ^ n
  have hJI : n ^ n * J = I := by
    dsimp [I,J]
    rw [← mul_pow, ← pow_succ']
    congr 2
    omega
  calc
    _ ≤ Fintype.card (Σ s : A → A, (x : A) → Row s x) :=
      Fintype.card_le_of_injective tableEncode tableEncode_injective
    _ = I + ∑ s ∈ Finset.univ.erase id, Fintype.card ((x : A) → Row s x) := by
      rw [Fintype.card_sigma, ← Finset.add_sum_erase _ _ (Finset.mem_univ id), id_count]
    _ ≤ I + ∑ _s ∈ Finset.univ.erase (id : A → A), J := by
      gcongr with s hs
      exact fixed_bound s (Finset.mem_erase.mp hs).1
    _ ≤ I + n ^ n * J := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      exact (Finset.card_erase_le).trans (by simp [n])
    _ = 2 * I := by rw [hJI]; omega


theorem count_bound_nat (hn : 2 ≤ Fintype.card A) :
    Nat.card {f : A → A → A // @Equation326 A ⟨f⟩} ≤
      2 * (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Nat.card_eq_fintype_card]
  exact count_bound hn

theorem cardinal_bound (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (FORecoveryCompactness.Tables Law326 (Fin n)) ≤
      2 * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) := by
  classical
  have e326 : FORecoveryCompactness.Tables Law326 (Fin n) ≃
      {f : Fin n → Fin n → Fin n // @Equation326 (Fin n) ⟨f⟩} :=
    Equiv.subtypeEquivRight (fun f => @Law326.models_iff (Fin n) ⟨f⟩)
  have e3 : FORecoveryCompactness.Tables Law3 (Fin n) ≃
      {f : Fin n → Fin n → Fin n // @Equation3 (Fin n) ⟨f⟩} :=
    Equiv.subtypeEquivRight (fun f => @Law3.models_iff (Fin n) ⟨f⟩)
  rw [Nat.card_congr e326, Nat.card_congr e3, EightRowCounting.count_idem_nat]
  exact count_bound_nat (by simpa using hn)

theorem negative : ¬ Law326.StructuralFrom Law8 := by
  apply FORecoveryCompactness.not_structural_of_unbounded_counts Law8 Law326
  intro K
  let n := 2 * K + 2
  refine ⟨n, by omega, ?_⟩
  calc
    K * Nat.card (FORecoveryCompactness.Tables Law326 (Fin n)) ≤
        K * (2 * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n))) :=
      Nat.mul_le_mul_left K (cardinal_bound n (by omega))
    _ < n * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) := by
      have hp := EightRowCounting.idem_count_pos n (by omega)
      dsimp [n]
      nlinarith
    _ ≤ _ := EightRowCounting.cardinal_bound n (by omega)


end SquareColumnCounting


theorem Equation326_not_StructuralFrom_Equation8_compactness :
    ¬ Law326.StructuralFrom Law8 := SquareColumnCounting.negative

/-- info: 'Equation326_not_StructuralFrom_Equation8_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation326_not_StructuralFrom_Equation8_compactness
