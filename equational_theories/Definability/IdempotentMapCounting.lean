import equational_theories.Definability.DiagonalTableCounting

/-!
# Arbitrary diagonals outnumber idempotent diagonals

An idempotent square map satisfies f(f(a)) = f(a) at any distinguished point.
Counting functions with this local condition gives at most 2 n^(n-1)
diagonals. With off-diagonal entries unrestricted, compactness rules out
FO-structural interpretation from E1 to E3659 on arbitrary magmas.
-/

open Law Law.MagmaLaw
namespace IdempotentMapCounting
variable {A : Type} [Fintype A] [DecidableEq A]
open DiagonalTableCounting

abbrev Row (a : A) := {f : A → A // f (f a) = f a}

def rowEquiv (a : A) : Row a ≃ Σ b : A, EventualRowCounting.ConstantFiber a b where
  toFun f := ⟨f.val a,f.val,rfl,f.property⟩
  invFun f := ⟨f.2.val,by rw [f.2.property.1,f.2.property.2]⟩
  left_inv _ := rfl
  right_inv f := by
    rcases f with ⟨b,f,hf,hg⟩
    dsimp
    subst b
    rfl

theorem row_count (a : A) : Fintype.card (Row a) =
    Fintype.card A ^ (Fintype.card A - 1) +
      (Fintype.card A - 1) * Fintype.card A ^ (Fintype.card A - 2) := by
  rw [Fintype.card_congr (rowEquiv a),Fintype.card_sigma,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have hself : Fintype.card (EventualRowCounting.ConstantFiber a a) =
      Fintype.card A ^ (Fintype.card A - 1) := by
    change Fintype.card (EightRowCounting.Fiber a a) = _
    rw [EightRowCounting.card_fiber,EightRowCounting.card_self_pair]
  rw [hself]
  congr 1
  calc
    _ = ∑ _b ∈ Finset.univ.erase a, Fintype.card A ^ (Fintype.card A - 2) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact EventualRowCounting.constant_count a b (Ne.symm (Finset.mem_erase.mp hb).1)
    _ = _ := by simp

theorem row_bound (a : A) (hn : 2 ≤ Fintype.card A) :
    Fintype.card (Row a) ≤ 2 * Fintype.card A ^ (Fintype.card A - 1) := by
  rw [row_count]
  have hp : Fintype.card A * Fintype.card A ^ (Fintype.card A - 2) =
      Fintype.card A ^ (Fintype.card A - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hh := Nat.mul_le_mul_right (Fintype.card A ^ (Fintype.card A - 2)) (Nat.sub_le (Fintype.card A) 1)
  rw [hp] at hh
  omega

def tableEncode (a : A) (f : FORecoveryCompactness.Tables Law3659 A) : Row a × OffTable (A := A) :=
  (⟨fun x => f.val x x,((@Law3659.models_iff A ⟨f.val⟩).mp f.property a).symm⟩,
    fun x y => f.val x y.val)

omit [Fintype A] in
theorem tableEncode_injective (a : A) : Function.Injective (tableEncode a) := by
  intro f g h
  have hh := congrArg (fun p : Row a × OffTable (A := A) => operation p.1.val p.2) h
  apply Subtype.ext
  funext x y
  have he := congrFun (congrFun hh x) y
  by_cases hxy : y = x
  · subst y; simpa only [operation,tableEncode,dif_pos rfl] using he
  · simpa only [operation,tableEncode,dif_neg hxy] using he

theorem upper_count (a : A) (hn : 2 ≤ Fintype.card A) :
    Nat.card (FORecoveryCompactness.Tables Law3659 A) ≤
      (2 * Fintype.card A ^ (Fintype.card A - 1)) *
        (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  have hh := Nat.card_le_card_of_injective (tableEncode a) (tableEncode_injective a)
  have hc : Nat.card (Row a × OffTable (A := A)) = Fintype.card (Row a) *
      (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
    rw [Nat.card_eq_fintype_card,Fintype.card_prod,off_count]
  rw [hc] at hh
  exact hh.trans (Nat.mul_le_mul_right _ (row_bound a hn))

def freeEncode (p : (A → A) × OffTable (A := A)) : FORecoveryCompactness.Tables Law1 A :=
  ⟨operation p.1 p.2,(@Law1.models_iff A ⟨operation p.1 p.2⟩).mpr (fun _ => rfl)⟩

omit [Fintype A] in
theorem freeEncode_injective : Function.Injective (freeEncode (A := A)) := by
  intro p q h
  exact operation_injective (congrArg Subtype.val h)

theorem lower_count :
    Fintype.card A ^ Fintype.card A *
      (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A ≤
        Nat.card (FORecoveryCompactness.Tables Law1 A) := by
  have hh := Nat.card_le_card_of_injective freeEncode (freeEncode_injective (A := A))
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fun,off_count] using hh

theorem negative : ¬ Law3659.StructuralFrom Law1 := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts Law1 Law3659 h
  let n := 2 * K + 4
  let I := n ^ (n - 1)
  let O := I ^ n
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hi : 0 < I := pow_pos (by omega) _
  have ho : 0 < O := pow_pos hi _
  have hu : Nat.card (FORecoveryCompactness.Tables Law3659 (Fin n)) ≤ (2 * I) * O := by
    simpa only [Fintype.card_fin] using upper_count (A := Fin n) 0 (by simpa using hn)
  have hl : n ^ n * O ≤ Nat.card (FORecoveryCompactness.Tables Law1 (Fin n)) := by
    simpa only [Fintype.card_fin] using lower_count (A := Fin n)
  have he : n ^ n = n * I := by
    dsimp [I]
    rw [← pow_succ']
    congr 1
  have hr : n * I ≤ (2 * K) * I := by
    refine Nat.le_of_mul_le_mul_right (c := O) ?_ ho
    rw [← he]
    calc
      _ ≤ Nat.card (FORecoveryCompactness.Tables Law1 (Fin n)) := hl
      _ ≤ K * Nat.card (FORecoveryCompactness.Tables Law3659 (Fin n)) := hK (Fin n)
      _ ≤ K * ((2 * I) * O) := Nat.mul_le_mul_left K hu
      _ = _ := by ac_rfl
  have hbad : n ≤ 2 * K := Nat.le_of_mul_le_mul_right hr hi
  dsimp [n] at hbad
  omega

end IdempotentMapCounting

theorem Equation3659_not_StructuralFrom_Equation1_compactness :
    ¬ Law3659.StructuralFrom Law1 := IdempotentMapCounting.negative

/-- info: 'Equation3659_not_StructuralFrom_Equation1_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3659_not_StructuralFrom_Equation1_compactness
