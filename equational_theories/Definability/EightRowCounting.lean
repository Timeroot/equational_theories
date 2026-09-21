import equational_theories.Equations.All
import equational_theories.Definability.FORecoveryCompactness
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

/-!
# Counting obstruction from E8 to idempotence

An E8 row has either a fixed diagonal point or a two-cycle through it. Counting
these choices gives an unbounded ratio to idempotent operation tables. The
compactness counting bound therefore rules out unrestricted FO-structural
recovery of E8 operations from idempotent ones.
-/

open Law Law.MagmaLaw
namespace EightRowCounting

variable {A : Type} [Fintype A] [DecidableEq A]

abbrev Row8 (a : A) := {f : A → A // f (f a) = a}
abbrev Fiber (a b : A) := {f : A → A // f a = b ∧ f b = a}
abbrev Outside (a b : A) := {z : A // z ∉ ({a,b} : Finset A)}

def rowEquiv (a : A) : Row8 a ≃ Σ b : A, Fiber a b where
  toFun f := ⟨f.val a, f.val, rfl, f.property⟩
  invFun f := ⟨f.2.val, by rw [f.2.property.1, f.2.property.2]⟩
  left_inv _ := rfl
  right_inv f := by
    rcases f with ⟨b, f, hf, hg⟩
    dsimp
    subst b
    rfl

noncomputable def fiberEquiv (a b : A) : Fiber a b ≃ (Outside a b → A) where
  toFun f z := f.val z.val
  invFun g := ⟨fun z => if ha : z = a then b else if hb : z = b then a
    else g ⟨z, by simp [ha, hb]⟩, by simp⟩
  left_inv f := by
    apply Subtype.ext
    funext z
    dsimp
    split_ifs with ha hb
    · subst z; exact f.property.1.symm
    · subst z; exact f.property.2.symm
    · rfl
  right_inv g := by
    funext z
    have hz := z.property
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    simp only [dif_neg hz.1, dif_neg hz.2]

theorem card_outside (a b : A) : Fintype.card (Outside a b) =
    Fintype.card A - ({a,b} : Finset A).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_subtype_compl (fun z : A => z ∈ ({a,b} : Finset A))

theorem card_fiber (a b : A) : Fintype.card (Fiber a b) =
    (Fintype.card A) ^ (Fintype.card A - ({a,b} : Finset A).card) := by
  rw [Fintype.card_congr (fiberEquiv a b), Fintype.card_fun, card_outside]

omit [Fintype A] in
theorem card_self_pair (a : A) : ({a,a} : Finset A).card = 1 := by simp

theorem card_row (a : A) : Fintype.card (Row8 a) =
    (Fintype.card A) ^ (Fintype.card A - 1) +
      (Fintype.card A - 1) * (Fintype.card A) ^ (Fintype.card A - 2) := by
  rw [Fintype.card_congr (rowEquiv a), Fintype.card_sigma,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a), card_fiber]
  simp only [card_self_pair]
  congr 1
  calc
    ∑ b ∈ Finset.univ.erase a, Fintype.card (Fiber a b) =
      ∑ _b ∈ Finset.univ.erase a, (Fintype.card A) ^ (Fintype.card A - 2) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hba := (Finset.mem_erase.mp hb).1
        rw [card_fiber]
        simp [Ne.symm hba]
    _ = _ := by simp

def tableEquiv : {f : A → A → A // @Equation8 A ⟨f⟩} ≃ ((a : A) → Row8 a) where
  toFun f a := ⟨f.val a, (f.property a).symm⟩
  invFun f := ⟨fun x y => (f x).val y, fun x => (f x).property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

def idemEquiv : {f : A → A → A // @Equation3 A ⟨f⟩} ≃ ((a : A) → Fiber a a) where
  toFun f a := ⟨f.val a, (f.property a).symm, (f.property a).symm⟩
  invFun f := ⟨fun x y => (f x).val y, fun x => (f x).property.1.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_eight : Fintype.card {f : A → A → A // @Equation8 A ⟨f⟩} =
    ((Fintype.card A) ^ (Fintype.card A - 1) +
      (Fintype.card A - 1) * (Fintype.card A) ^ (Fintype.card A - 2)) ^ Fintype.card A := by
  rw [Fintype.card_congr tableEquiv, Fintype.card_pi]
  simp only [card_row, Finset.prod_const, Finset.card_univ]

theorem count_idem : Fintype.card {f : A → A → A // @Equation3 A ⟨f⟩} =
    ((Fintype.card A) ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Fintype.card_congr idemEquiv, Fintype.card_pi]
  simp only [card_fiber, card_self_pair,
    Finset.prod_const, Finset.card_univ]


theorem count_eight_nat : Nat.card {f : A → A → A // @Equation8 A ⟨f⟩} =
    ((Fintype.card A) ^ (Fintype.card A - 1) +
      (Fintype.card A - 1) * (Fintype.card A) ^ (Fintype.card A - 2)) ^ Fintype.card A := by
  rw [Nat.card_eq_fintype_card, count_eight]

theorem count_idem_nat : Nat.card {f : A → A → A // @Equation3 A ⟨f⟩} =
    ((Fintype.card A) ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Nat.card_eq_fintype_card, count_idem]


theorem numerical_bound (n : ℕ) (hn : 2 ≤ n) :
    n * (n ^ (n - 1)) ^ n ≤ (n ^ (n - 1) + (n - 1) * n ^ (n - 2)) ^ n := by
  let I := n ^ (n - 1)
  let m := n ^ (n - 2)
  have hI : I = n * m := by
    change n ^ (n - 1) = n * n ^ (n - 2)
    rw [← pow_succ']
    congr 1
    omega
  have hp : I ^ (n - 1) * I = I ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have hs : n - 1 + 1 = n := by omega
  have he : n * I ^ n = I ^ n + n * I ^ (n - 1) * ((n - 1) * m) := by
    calc
      n * I ^ n = (n - 1 + 1) * (I ^ (n - 1) * I) := by rw [hs, hp]
      _ = I ^ (n - 1) * I + n * I ^ (n - 1) * ((n - 1) * m) := by rw [hI]; ring
      _ = _ := by rw [hp]
  change n * I ^ n ≤ (I + (n - 1) * m) ^ n
  rw [he]
  exact pow_add_mul_le_add_pow (Nat.zero_le I) (Nat.zero_le _) n

theorem cardinal_bound (n : ℕ) (hn : 2 ≤ n) :
    n * Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) ≤
      Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) := by
  classical
  have e3 : FORecoveryCompactness.Tables Law3 (Fin n) ≃
      {f : Fin n → Fin n → Fin n // @Equation3 (Fin n) ⟨f⟩} :=
    Equiv.subtypeEquivRight (fun f => @Law3.models_iff (Fin n) ⟨f⟩)
  have e8 : FORecoveryCompactness.Tables Law8 (Fin n) ≃
      {f : Fin n → Fin n → Fin n // @Equation8 (Fin n) ⟨f⟩} :=
    Equiv.subtypeEquivRight (fun f => @Law8.models_iff (Fin n) ⟨f⟩)
  have c3 := (Nat.card_congr e3).trans (count_idem_nat (A := Fin n))
  have c8 := (Nat.card_congr e8).trans (count_eight_nat (A := Fin n))
  rw [c3, c8, Fintype.card_fin]
  exact numerical_bound n hn

theorem idem_count_pos (n : ℕ) (hn : 0 < n) :
    0 < Nat.card (FORecoveryCompactness.Tables Law3 (Fin n)) := by
  classical
  have e3 : FORecoveryCompactness.Tables Law3 (Fin n) ≃
      {f : Fin n → Fin n → Fin n // @Equation3 (Fin n) ⟨f⟩} :=
    Equiv.subtypeEquivRight (fun f => @Law3.models_iff (Fin n) ⟨f⟩)
  have c3 := (Nat.card_congr e3).trans (count_idem_nat (A := Fin n))
  rw [c3, Fintype.card_fin]
  positivity

theorem negative : ¬ Law3.StructuralFrom Law8 := by
  apply FORecoveryCompactness.not_structural_of_unbounded_counts Law8 Law3
  intro K
  refine ⟨K + 2, by omega, ?_⟩
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (by omega)
    (idem_count_pos (K + 2) (by omega))) (cardinal_bound (K + 2) (by omega))

end EightRowCounting

open Law Law.MagmaLaw

theorem Equation3_not_StructuralFrom_Equation8_compactness :
    ¬ Law3.StructuralFrom Law8 := EightRowCounting.negative

/-- info: 'Equation3_not_StructuralFrom_Equation8_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3_not_StructuralFrom_Equation8_compactness
