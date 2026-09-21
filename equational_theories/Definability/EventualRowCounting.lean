import equational_theories.Definability.EightRowCounting
import Mathlib.Data.Fintype.Sum

/-!
# Counting rows with eventual two-cycles

Rows whose diagonal orbit is a two-cycle or reaches a fixed point satisfy
E3253. These disjoint families give an unbounded ratio to E8 operation tables,
so E3253 does not FO-structurally imply E8 on arbitrary magmas.
-/

open Law Law.MagmaLaw
namespace EventualRowCounting
variable {A : Type} [Fintype A] [DecidableEq A]

abbrev Row (a : A) := {f : A → A // f (f (f a)) = f a}
abbrev ConstantFiber (a b : A) := {f : A → A // f a = b ∧ f b = b}
abbrev Extra (a : A) := Σ b : {b : A // b ≠ a}, ConstantFiber a b.val

noncomputable def constantEquiv (a b : A) : ConstantFiber a b ≃ (EightRowCounting.Outside a b → A) where
  toFun f z := f.val z.val
  invFun g := ⟨fun z => if ha : z = a then b else if hb : z = b then b
    else g ⟨z, by simp [ha,hb]⟩, by simp⟩
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

theorem constant_count (a b : A) (hab : a ≠ b) :
    Fintype.card (ConstantFiber a b) = Fintype.card A ^ (Fintype.card A - 2) := by
  rw [Fintype.card_congr (constantEquiv a b), Fintype.card_fun,
    EightRowCounting.card_outside, Finset.card_pair hab]

theorem extra_count (a : A) : Fintype.card (Extra a) =
    (Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2) := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ _b : {b : A // b ≠ a}, Fintype.card A ^ (Fintype.card A - 2) := by
      apply Finset.sum_congr rfl
      intro b _
      exact constant_count a b.val b.property.symm
    _ = _ := by simp [Fintype.card_subtype_compl]


def rowEncode (a : A) : EightRowCounting.Row8 a ⊕ Extra a → Row a
  | .inl f => ⟨f.val, by rw [f.property]⟩
  | .inr ⟨b,f⟩ => ⟨f.val, by rw [f.property.1, f.property.2, f.property.2]⟩

omit [Fintype A] [DecidableEq A] in
theorem rowEncode_injective (a : A) : Function.Injective (rowEncode a) := by
  intro f g h
  have hv := congrArg Subtype.val h
  cases f with
  | inl f =>
    cases g with
    | inl g => exact congrArg Sum.inl (Subtype.ext hv)
    | inr g =>
      exfalso
      have hf := f.property
      change f.val = g.2.val at hv
      rw [hv, g.2.property.1, g.2.property.2] at hf
      exact g.1.property hf
  | inr f =>
    cases g with
    | inl g =>
      exfalso
      have hg := g.property
      change f.2.val = g.val at hv
      rw [← hv, f.2.property.1, f.2.property.2] at hg
      exact f.1.property hg
    | inr g =>
      congr 1
      rcases f with ⟨⟨b,hb⟩,f⟩
      rcases g with ⟨⟨c,hc⟩,g⟩
      change f.val = g.val at hv
      have hbc : b = c := f.property.1.symm.trans ((congrFun hv a).trans g.property.1)
      subst c
      congr 1
      exact Subtype.ext hv

theorem row_bound (a : A) :
    Fintype.card A ^ (Fintype.card A - 1) +
      2 * ((Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2)) ≤
        Fintype.card (Row a) := by
  have hh := Fintype.card_le_of_injective (rowEncode a) (rowEncode_injective a)
  rw [Fintype.card_sum, EightRowCounting.card_row, extra_count] at hh
  omega

def tableEquiv : {f : A → A → A // @Equation3253 A ⟨f⟩} ≃ ((a : A) → Row a) where
  toFun f a := ⟨f.val a, (f.property a).symm⟩
  invFun f := ⟨fun x y => (f x).val y, fun x => (f x).property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_bound :
    (Fintype.card A ^ (Fintype.card A - 1) +
      2 * ((Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2))) ^ Fintype.card A ≤
        Fintype.card {f : A → A → A // @Equation3253 A ⟨f⟩} := by
  rw [Fintype.card_congr tableEquiv, Fintype.card_pi]
  calc
    _ = ∏ _a : A, (Fintype.card A ^ (Fintype.card A - 1) +
      2 * ((Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2))) := by simp
    _ ≤ _ := Finset.prod_le_prod (by intros; omega) (fun a _ => row_bound a)

theorem count_bound_nat :
    (Fintype.card A ^ (Fintype.card A - 1) +
      2 * ((Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2))) ^ Fintype.card A ≤
        Nat.card {f : A → A → A // @Equation3253 A ⟨f⟩} := by
  rw [Nat.card_eq_fintype_card]
  exact count_bound

theorem numerical_bound (n : ℕ) (hn : 2 ≤ n) :
    n * (n ^ (n - 1) + (n - 1) * n ^ (n - 2)) ^ n ≤
      3 * (n ^ (n - 1) + 2 * ((n - 1) * n ^ (n - 2))) ^ n := by
  let m := n ^ (n - 2)
  let J := (n - 1) * m
  let R := n ^ (n - 1) + J
  have hI : n ^ (n - 1) = n * m := by
    dsimp [m]
    rw [← pow_succ']
    congr 1
    omega
  have h3 : R ≤ 3 * J := by
    dsimp [R,J]
    rw [hI]
    have hh : n ≤ 2 * (n - 1) := by omega
    nlinarith [Nat.mul_le_mul_right m hh]
  have hp : R ^ (n - 1) * R = R ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have hb := pow_add_mul_le_add_pow (a := R) (b := J) (Nat.zero_le R) (Nat.zero_le _) n
  norm_num only [Nat.cast_id] at hb
  have hc := Nat.mul_le_mul_left (n * R ^ (n - 1)) h3
  have he : n * R ^ (n - 1) * R = n * R ^ n := by rw [Nat.mul_assoc, hp]
  rw [he] at hc
  have hh : n * R ^ n ≤ 3 * (R + J) ^ n := by
    calc
      _ ≤ n * R ^ (n - 1) * (3 * J) := hc
      _ = 3 * (n * R ^ (n - 1) * J) := by ring
      _ ≤ 3 * (R ^ n + n * R ^ (n - 1) * J) := Nat.mul_le_mul_left 3 (Nat.le_add_left _ _)
      _ ≤ _ := Nat.mul_le_mul_left 3 hb
  convert hh using 2
  dsimp [R,J]
  congr 1
  ring

theorem cardinal_bound (n : ℕ) (hn : 2 ≤ n) :
    n * Nat.card (FORecoveryCompactness.Tables Law8 (Fin n)) ≤
      3 * Nat.card (FORecoveryCompactness.Tables Law3253 (Fin n)) := by
  classical
  have e8 : FORecoveryCompactness.Tables Law8 (Fin n) ≃
      {f : Fin n → Fin n → Fin n // @Equation8 (Fin n) ⟨f⟩} :=
    Equiv.subtypeEquivRight (fun f => @Law8.models_iff (Fin n) ⟨f⟩)
  have e3253 : FORecoveryCompactness.Tables Law3253 (Fin n) ≃
      {f : Fin n → Fin n → Fin n // @Equation3253 (Fin n) ⟨f⟩} :=
    Equiv.subtypeEquivRight (fun f => @Law3253.models_iff (Fin n) ⟨f⟩)
  rw [Nat.card_congr e8, EightRowCounting.count_eight_nat, Nat.card_congr e3253,
    Fintype.card_fin]
  exact (numerical_bound n hn).trans (Nat.mul_le_mul_left 3
    (by simpa only [Fintype.card_fin] using count_bound_nat (A := Fin n)))

theorem negative : ¬ Law8.StructuralFrom Law3253 := by
  apply FORecoveryCompactness.not_structural_of_unbounded_counts Law3253 Law8
  intro K
  let n := 3 * K + 2
  refine ⟨n, by omega, ?_⟩
  have hb := cardinal_bound n (by omega)
  have h8 := EightRowCounting.cardinal_bound n (by omega)
  have h3 := EightRowCounting.idem_count_pos n (by omega)
  have hn : 0 < n := by omega
  have hp := Nat.mul_pos hn h3
  dsimp [n] at hb
  nlinarith


end EventualRowCounting


theorem Equation8_not_StructuralFrom_Equation3253_compactness :
    ¬ Law8.StructuralFrom Law3253 := EventualRowCounting.negative

/-- info: 'Equation8_not_StructuralFrom_Equation3253_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation8_not_StructuralFrom_Equation3253_compactness
