import equational_theories.Definability.EightRowCounting

/-!
# Counting all operation tables against E8

The proportion of operation tables satisfying E8 tends to zero. The uniform
counting bound from compactness therefore refutes E1 → E8 structurally on
arbitrary magmas.
-/

open Law Law.MagmaLaw
namespace UnrestrictedRowCounting
variable {A : Type} [Fintype A] [DecidableEq A]

def allEquiv : FORecoveryCompactness.Tables Law1 A ≃ (A → A → A) where
  toFun f := f.val
  invFun f := ⟨f, (@Law1.models_iff A ⟨f⟩).mpr (fun _ => rfl)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_all_nat : Nat.card (FORecoveryCompactness.Tables Law1 A) =
    (Fintype.card A ^ Fintype.card A) ^ Fintype.card A := by
  rw [Nat.card_congr allEquiv, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun]

theorem numerical_bound (n : ℕ) (hn : 4 ≤ n) :
    n * (n ^ (n - 1) + (n - 1) * n ^ (n - 2)) ^ n ≤ (n ^ n) ^ n := by
  let m := n ^ (n - 2)
  let R := n ^ (n - 1) + (n - 1) * m
  have hI : n ^ (n - 1) = n * m := by
    dsimp [m]
    rw [← pow_succ']
    congr 1
    omega
  have hT : n ^ n = n * (n * m) := by
    rw [← hI, ← pow_succ']
    congr 1
    omega
  have hR : 2 * R ≤ n ^ n := by
    dsimp [R]
    rw [hI,hT]
    have hh : 2 * (n + (n - 1)) ≤ n * n := by nlinarith [Nat.mul_le_mul_left n hn, Nat.sub_le n 1]
    nlinarith [Nat.mul_le_mul_right m hh]
  calc
    n * R ^ n ≤ 2 ^ n * R ^ n := Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)
    _ = (2 * R) ^ n := (mul_pow _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_left hR n

theorem cardinal_bound (n : ℕ) (hn : 4 ≤ n) :
    n * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      Nat.card (FORecoveryCompactness.Tables Law1 (Fin n)) := by
  classical
  have e8 : FORecoveryCompactness.Tables Law8 (Fin n) ≃
      {f : Fin n → Fin n → Fin n // @Equation8 (Fin n) ⟨f⟩} :=
    Equiv.subtypeEquivRight (fun f => @Law8.models_iff (Fin n) ⟨f⟩)
  rw [Nat.card_congr e8, EightRowCounting.count_eight_nat, count_all_nat, Fintype.card_fin]
  exact numerical_bound n hn

theorem negative : ¬ Law8.StructuralFrom Law1 := by
  apply FORecoveryCompactness.not_structural_of_unbounded_counts Law1 Law8
  intro K
  let n := K + 4
  refine ⟨n, by omega, ?_⟩
  have h8 := EightRowCounting.cardinal_bound n (by omega)
  have h3 := EightRowCounting.idem_count_pos n (by omega)
  have hn : 0 < n := by omega
  have hp : 0 < Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) :=
    lt_of_lt_of_le (Nat.mul_pos hn h3) h8
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (by omega) hp)
    (cardinal_bound n (by omega))

end UnrestrictedRowCounting

theorem Equation8_not_StructuralFrom_Equation1_compactness :
    ¬ Law8.StructuralFrom Law1 := UnrestrictedRowCounting.negative

/-- info: 'Equation8_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation8_not_StructuralFrom_Equation1_compactness
