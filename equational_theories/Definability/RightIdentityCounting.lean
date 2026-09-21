import equational_theories.Definability.FORecoveryCompactness
import equational_theories.Equations.All
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# A counting obstruction from E11 to E109

In an E109 magma, squares are right identities and every row indexed by a right
identity takes values among the right identities. Encoding those entries gives
at most 2^n n^((n-1)(n-2)) tables. E11 admits at least
n^(n-1) n^((n-1)(n-2)) tables, an unbounded ratio. Compactness therefore refutes
unrestricted FO-structural interpretation from E11 to E109.
-/

open Law Law.MagmaLaw
namespace RightIdentityCounting
variable {A : Type} [Fintype A] [DecidableEq A]
abbrev Inside (S : Finset A) := {x : A // x ∈ S}
abbrev Outside (S : Finset A) := {x : A // x ∉ S}
abbrev OffDiag {S : Finset A} (x : Outside S) := {y : Outside S // y ≠ x}
abbrev Code (S : Finset A) :=
  (Inside S → Outside S → Inside S) × (Outside S → Inside S) ×
    ((x : Outside S) → OffDiag x → A)

abbrev Fixed (S : Finset A) := {f : A → A → A //
  (∀ y ∈ S, ∀ x, f x y = x) ∧ (∀ x, f x x ∈ S) ∧
    (∀ x ∈ S, ∀ y, f x y ∈ S)}

def encode (S : Finset A) (f : Fixed S) : Code S :=
  (fun x y => ⟨f.val x y, f.property.2.2 x x.property y⟩,
   fun x => ⟨f.val x x, f.property.2.1 x⟩,
   fun x y => f.val x y.val)

def decode (S : Finset A) (c : Code S) (x y : A) : A :=
  if hy : y ∈ S then x
  else if hx : x ∈ S then (c.1 ⟨x,hx⟩ ⟨y,hy⟩).val
  else if hxy : y = x then (c.2.1 ⟨x,hx⟩).val
  else c.2.2 ⟨x,hx⟩ ⟨⟨y,hy⟩, fun h => hxy (congrArg Subtype.val h)⟩

omit [Fintype A] in
theorem decode_encode (S : Finset A) (f : Fixed S) : decode S (encode S f) = f.val := by
  funext x y
  dsimp [decode,encode]
  split_ifs with hy hx hxy
  · exact (f.property.1 y hy x).symm
  · rfl
  · subst y; rfl
  · rfl

omit [Fintype A] in
theorem encode_injective (S : Finset A) : Function.Injective (encode S) := by
  intro f g h
  apply Subtype.ext
  rw [← decode_encode S f, ← decode_encode S g, h]

theorem card_outside (S : Finset A) : Fintype.card (Outside S) = Fintype.card A - S.card := by
  simpa only [Fintype.card_coe] using Fintype.card_subtype_compl (fun x : A => x ∈ S)

theorem card_offdiag {S : Finset A} (x : Outside S) :
    Fintype.card (OffDiag x) = Fintype.card (Outside S) - 1 := by
  simp [OffDiag, Fintype.card_subtype_compl]

theorem card_code (S : Finset A) : Fintype.card (Code S) =
    S.card ^ ((S.card + 1) * (Fintype.card A - S.card)) *
      Fintype.card A ^ ((Fintype.card A - S.card) * (Fintype.card A - S.card - 1)) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_pi]
  simp only [card_offdiag, Fintype.card_fun, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, card_outside]
  rw [← pow_mul, ← pow_mul]
  rw [← Nat.mul_assoc, ← pow_add]
  congr 2 <;> ring

noncomputable def rightIds (f : A → A → A) : Finset A :=
  Finset.univ.filter (fun y => ∀ x, f x y = x)

theorem mem_rightIds (f : A → A → A) (y : A) :
    y ∈ rightIds f ↔ ∀ x, f x y = x := by
  classical
  simp [rightIds]

theorem rightIds_nonempty [Nonempty A] (f : A → A → A) (hf : @Equation109 A ⟨f⟩) :
    (rightIds f).Nonempty := by
  let a : A := Classical.choice ‹Nonempty A›
  exact ⟨f (f a a) a, (mem_rightIds f _).mpr (fun x => (hf x a a).symm)⟩

theorem fixed_of_equation [Nonempty A] (f : A → A → A) (hf : @Equation109 A ⟨f⟩) :
    (∀ y ∈ rightIds f, ∀ x, f x y = x) ∧ (∀ x, f x x ∈ rightIds f) ∧
      (∀ x ∈ rightIds f, ∀ y, f x y ∈ rightIds f) := by
  obtain ⟨r,hr⟩ := rightIds_nonempty f hf
  have hr := (mem_rightIds f r).mp hr
  refine ⟨fun y hy => (mem_rightIds f y).mp hy, ?_, ?_⟩
  · intro y
    apply (mem_rightIds f _).mpr
    intro x
    have h := hf x y r
    change x = f x (f (f y y) r) at h
    rw [hr] at h
    exact h.symm
  · intro r hr y
    have hrr := (mem_rightIds f r).mp hr r
    apply (mem_rightIds f _).mpr
    intro x
    have h := hf x r y
    change x = f x (f (f r r) y) at h
    rw [hrr] at h
    exact h.symm

noncomputable def tableEncode [Nonempty A] (f : {f : A → A → A // @Equation109 A ⟨f⟩}) :
    Σ S : {S : Finset A // S.Nonempty}, Code S.val :=
  ⟨⟨rightIds f.val, rightIds_nonempty f.val f.property⟩,
    encode _ ⟨f.val, fixed_of_equation f.val f.property⟩⟩

theorem tableEncode_injective [Nonempty A] : Function.Injective (tableEncode (A := A)) := by
  intro f g h
  have hd := congrArg (fun p : Σ S : {S : Finset A // S.Nonempty}, Code S.val =>
    decode p.1.val p.2) h
  apply Subtype.ext
  simpa only [tableEncode, decode_encode] using hd

theorem numerical_code_bound (n k : ℕ) (hn : 8 ≤ n) (hk : 0 < k) (hkn : k ≤ n) :
    k ^ ((k + 1) * (n - k)) * n ^ ((n - k) * (n - k - 1)) ≤
      n ^ ((n - 1) * (n - 2)) := by
  have hn1 : 1 ≤ n := by omega
  have h1 : n - 1 + 1 = n := by omega
  have h2 : n - 2 + 2 = n := by omega
  have h3 : n - 3 + 3 = n := by omega
  by_cases hk1 : k = 1
  · subst k
    simp [Nat.sub_sub]
  by_cases hk2 : k = 2
  · subst k
    have hp : 2 ^ ((2 + 1) * (n - 2)) ≤ n ^ (n - 2) := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left hn _
    calc
      _ ≤ n ^ (n - 2) * n ^ ((n - 2) * (n - 2 - 1)) := Nat.mul_le_mul_right _ hp
      _ = n ^ ((n - 2) + (n - 2) * (n - 3)) := by rw [← pow_add]; congr 2
      _ ≤ _ := Nat.pow_le_pow_right hn1 (by nlinarith)
  have hk3 : 3 ≤ k := by omega
  have hsum : (k + 1) * (n - k) + (n - k) * (n - k - 1) = n * (n - k) := by
    by_cases hm : n - k = 0
    · simp [hm]
    · have hm1 : n - k - 1 + 1 = n - k := by omega
      have hnk : n - k + k = n := by omega
      nlinarith
  calc
    _ ≤ n ^ ((k + 1) * (n - k)) * n ^ ((n - k) * (n - k - 1)) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hkn _)
    _ = n ^ (n * (n - k)) := by rw [← pow_add, hsum]
    _ ≤ n ^ (n * (n - 3)) := Nat.pow_le_pow_right hn1 (Nat.mul_le_mul_left n (by omega))
    _ ≤ _ := Nat.pow_le_pow_right hn1 (by nlinarith)

theorem upper_count [Nonempty A] (hn : 8 ≤ Fintype.card A) :
    Fintype.card {f : A → A → A // @Equation109 A ⟨f⟩} ≤
      2 ^ Fintype.card A * Fintype.card A ^ ((Fintype.card A - 1) * (Fintype.card A - 2)) := by
  classical
  calc
    _ ≤ Fintype.card (Σ S : {S : Finset A // S.Nonempty}, Code S.val) :=
      Fintype.card_le_of_injective tableEncode tableEncode_injective
    _ = ∑ S : {S : Finset A // S.Nonempty}, Fintype.card (Code S.val) := Fintype.card_sigma
    _ ≤ ∑ _S : {S : Finset A // S.Nonempty},
        Fintype.card A ^ ((Fintype.card A - 1) * (Fintype.card A - 2)) := by
      apply Finset.sum_le_sum
      intro S _
      rw [card_code]
      exact numerical_code_bound _ _ hn (Finset.card_pos.mpr S.property) S.val.card_le_univ
    _ = Fintype.card {S : Finset A // S.Nonempty} *
        Fintype.card A ^ ((Fintype.card A - 1) * (Fintype.card A - 2)) := by simp
    _ ≤ _ := by
      apply Nat.mul_le_mul_right
      simpa using Fintype.card_subtype_le (fun S : Finset A => S.Nonempty)


abbrev LowerCode (a : A) := (Outside {a} → A) × ((x : Outside {a}) → OffDiag x → A)

def lowerOp (a : A) (c : LowerCode a) (x y : A) : A :=
  if hy : y = a then x
  else if hx : x = a then c.1 ⟨y, by simpa using hy⟩
  else if hxy : y = x then a
  else c.2 ⟨x, by simpa using hx⟩
    ⟨⟨y, by simpa using hy⟩, fun h => hxy (congrArg Subtype.val h)⟩

omit [Fintype A] in
theorem lower_square (a : A) (c : LowerCode a) (x : A) : lowerOp a c x x = a := by
  by_cases hx : x = a
  · subst x; simp [lowerOp]
  · simp [lowerOp,hx]

def lowerEncode (a : A) (c : LowerCode a) : {f : A → A → A // @Equation11 A ⟨f⟩} :=
  ⟨lowerOp a c, by
    intro x y
    change x = lowerOp a c x (lowerOp a c y y)
    rw [lower_square]
    simp [lowerOp]⟩

omit [Fintype A] in
theorem lowerEncode_injective (a : A) : Function.Injective (lowerEncode a) := by
  intro c d h
  have hv := congrArg Subtype.val h
  apply Prod.ext
  · funext y
    have hy : y.val ≠ a := by simpa using y.property
    have hh := congrFun (congrFun hv a) y.val
    simpa only [lowerEncode, lowerOp, dif_neg hy, dif_pos rfl] using hh
  · funext x y
    have hx : x.val ≠ a := by simpa using x.property
    have hy : y.val.val ≠ a := by simpa using y.val.property
    have hxy : y.val.val ≠ x.val := fun h => y.property (Subtype.ext h)
    have hh := congrFun (congrFun hv x.val) y.val.val
    simpa only [lowerEncode, lowerOp, dif_neg hy, dif_neg hx, dif_neg hxy] using hh

theorem lower_count (a : A) :
    Fintype.card A ^ (Fintype.card A - 1) *
      Fintype.card A ^ ((Fintype.card A - 1) * (Fintype.card A - 2)) ≤
        Fintype.card {f : A → A → A // @Equation11 A ⟨f⟩} := by
  have hh := Fintype.card_le_of_injective (lowerEncode a) (lowerEncode_injective a)
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_pi] at hh
  simp only [Fintype.card_fun, card_offdiag, Finset.prod_const, Finset.card_univ,
    card_outside, Finset.card_singleton, ← pow_mul, Nat.sub_sub, Nat.reduceAdd] at hh
  simpa only [Nat.mul_comm] using hh

theorem numerical_ratio (n : ℕ) (hn : 4 ≤ n) : n * 2 ^ n ≤ n ^ (n - 1) := by
  have he : n - 2 + 1 = n - 1 := by omega
  rw [← he, pow_succ']
  apply Nat.mul_le_mul_left
  calc
    2 ^ n ≤ 2 ^ (2 * (n - 2)) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 4 ^ (n - 2) := by rw [pow_mul]; rfl
    _ ≤ _ := Nat.pow_le_pow_left hn _

theorem count_comparison [Nonempty A] (hn : 8 ≤ Fintype.card A) :
    Fintype.card A * Fintype.card {f : A → A → A // @Equation109 A ⟨f⟩} ≤
      Fintype.card {f : A → A → A // @Equation11 A ⟨f⟩} := by
  let n := Fintype.card A
  let X := n ^ ((n - 1) * (n - 2))
  calc
    _ ≤ n * (2 ^ n * X) := Nat.mul_le_mul_left _ (upper_count hn)
    _ = (n * 2 ^ n) * X := (Nat.mul_assoc _ _ _).symm
    _ ≤ n ^ (n - 1) * X := Nat.mul_le_mul_right X (numerical_ratio n (by omega))
    _ ≤ _ := lower_count (Classical.choice ‹Nonempty A›)


theorem count_comparison_nat [Nonempty A] (hn : 8 ≤ Fintype.card A) :
    Fintype.card A * Nat.card {f : A → A → A // @Equation109 A ⟨f⟩} ≤
      Nat.card {f : A → A → A // @Equation11 A ⟨f⟩} := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact count_comparison hn

theorem cardinal_bound (n : ℕ) (hn : 8 ≤ n) :
    n * Nat.card (FORecoveryCompactness.Tables Law109 (Fin n)) ≤
      Nat.card (FORecoveryCompactness.Tables Law11 (Fin n)) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  have e11 : FORecoveryCompactness.Tables Law11 (Fin n) ≃
      {f : Fin n → Fin n → Fin n // @Equation11 (Fin n) ⟨f⟩} :=
    Equiv.subtypeEquivRight (fun f => @Law11.models_iff (Fin n) ⟨f⟩)
  have e109 : FORecoveryCompactness.Tables Law109 (Fin n) ≃
      {f : Fin n → Fin n → Fin n // @Equation109 (Fin n) ⟨f⟩} :=
    Equiv.subtypeEquivRight (fun f => @Law109.models_iff (Fin n) ⟨f⟩)
  rw [Nat.card_congr e11, Nat.card_congr e109]
  simpa only [Fintype.card_fin] using count_comparison_nat (A := Fin n) (by simpa using hn)

theorem negative : ¬ Law109.StructuralFrom Law11 := by
  apply FORecoveryCompactness.not_structural_of_unbounded_counts Law11 Law109
  intro K
  let n := K + 8
  refine ⟨n, by omega, ?_⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (FORecoveryCompactness.Tables Law109 (Fin n)) :=
    ⟨⟨fun x _ => x, (@Law109.models_iff (Fin n) ⟨fun x _ => x⟩).mpr (fun _ _ _ => rfl)⟩⟩
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (by omega) Nat.card_pos)
    (cardinal_bound n (by omega))


end RightIdentityCounting


theorem Equation109_not_StructuralFrom_Equation11_compactness :
    ¬ Law109.StructuralFrom Law11 := RightIdentityCounting.negative

/-- info: 'Equation109_not_StructuralFrom_Equation11_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation109_not_StructuralFrom_Equation11_compactness
