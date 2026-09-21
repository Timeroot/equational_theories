import equational_theories.Definability.EventualRowUpperCounting
import equational_theories.Equations.All
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-!
# Diagonal families obstruct unrestricted FO recovery

Off-diagonal entries are independent for laws constraining only the square map.
Idempotent retractions and block involutions supply more operation tables than
E3253 can admit under the uniform bound imposed by FO compactness. This proves
E3659 → E3253 and E151 → E3253 false on arbitrary magmas.
-/

open Law Law.MagmaLaw
namespace DiagonalTableCounting
variable {A : Type} [Fintype A] [DecidableEq A]

abbrev OffTable := (x : A) → {y : A // y ≠ x} → A

def operation (d : A → A) (f : OffTable (A := A)) (x y : A) : A :=
  if h : y = x then d x else f x ⟨y,h⟩

omit [Fintype A] in
@[simp] theorem square (d : A → A) (f : OffTable (A := A)) (x : A) :
    operation d f x x = d x := by simp [operation]

omit [Fintype A] in
theorem operation_injective : Function.Injective
    (fun p : (A → A) × OffTable (A := A) => operation p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · funext x
    have hh := congrFun (congrFun h x) x
    simpa only [square] using hh
  · funext x y
    have hh := congrFun (congrFun h x) y.val
    simpa only [operation,dif_neg y.property] using hh

theorem off_count : Fintype.card (OffTable (A := A)) =
    (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Fintype.card_pi]
  simp [Fintype.card_subtype_compl]

omit [Fintype A] in
theorem satisfies_3659 (d : A → A) (f : OffTable (A := A)) (hd : ∀ x, d (d x) = d x) :
    @Equation3659 A ⟨operation d f⟩ := by
  intro x
  change operation d f x x = operation d f (operation d f x x) (operation d f x x)
  simp [hd]

omit [Fintype A] in
theorem satisfies_151 (d : A → A) (f : OffTable (A := A)) (hd : ∀ x, d (d x) = x) :
    @Equation151 A ⟨operation d f⟩ := by
  intro x
  change x = operation d f (operation d f x x) (operation d f x x)
  simp [hd]

def retractDiag (r m : ℕ) (f : Fin m → Fin r) : Fin r ⊕ Fin m → Fin r ⊕ Fin m
  | .inl x => .inl x
  | .inr x => .inl (f x)

theorem retractDiag_idempotent (r m : ℕ) (f : Fin m → Fin r) (x : Fin r ⊕ Fin m) :
    retractDiag r m f (retractDiag r m f x) = retractDiag r m f x := by cases x <;> rfl

def retractEncode (r m : ℕ) (p : (Fin m → Fin r) × OffTable (A := Fin r ⊕ Fin m)) :
    FORecoveryCompactness.Tables Law3659 (Fin r ⊕ Fin m) :=
  ⟨operation (retractDiag r m p.1) p.2,
    (@Law3659.models_iff _ ⟨operation (retractDiag r m p.1) p.2⟩).mpr
      (satisfies_3659 _ _ (retractDiag_idempotent r m p.1))⟩

theorem retractEncode_injective (r m : ℕ) : Function.Injective (retractEncode r m) := by
  intro p q h
  have he : (retractDiag r m p.1, p.2) = (retractDiag r m q.1, q.2) :=
    operation_injective (congrArg Subtype.val h)
  apply Prod.ext
  · funext x
    have hh := congrFun (congrArg Prod.fst he) (Sum.inr x)
    exact Sum.inl.inj hh
  · exact (Prod.mk.inj he).2

theorem retract_count (r m : ℕ) :
    r ^ m * ((r + m) ^ (r + m - 1)) ^ (r + m) ≤
      Nat.card (FORecoveryCompactness.Tables Law3659 (Fin r ⊕ Fin m)) := by
  have hh := Nat.card_le_card_of_injective (retractEncode r m) (retractEncode_injective r m)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    off_count,Fintype.card_sum] using hh

theorem numerical_retract (m : ℕ) : (5 + m) * 4 ^ (5 + m) ≤ 12500 * 5 ^ m := by
  let n := 5 + m
  have hp : 4 ^ (n - 1) * 4 = 4 ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have hb := pow_add_mul_le_add_pow (a := (4 : ℕ)) (b := 1) (by omega) (by omega) n
  norm_num only [Nat.cast_id, Nat.mul_one, Nat.reduceAdd] at hb
  change n * 4 ^ n ≤ _
  calc
    n * 4 ^ n = 4 * (n * 4 ^ (n - 1)) := by rw [← hp]; ring
    _ ≤ 4 * (4 ^ n + n * 4 ^ (n - 1)) := Nat.mul_le_mul_left 4 (Nat.le_add_left _ _)
    _ ≤ 4 * 5 ^ n := Nat.mul_le_mul_left 4 hb
    _ = _ := by dsimp [n]; rw [pow_add]; norm_num; ring

theorem retract_negative_of_upper (B : NatMagmaLaw)
    (hB : ∀ (G : Type) [Fintype G] [Nonempty G], 3 ≤ Fintype.card G →
      Nat.card (FORecoveryCompactness.Tables B G) ≤ 4 ^ Fintype.card G *
        (Fintype.card G ^ (Fintype.card G - 1)) ^ Fintype.card G) :
    ¬ B.StructuralFrom Law3659 := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts Law3659 B h
  let m := 12500 * K + 1
  let G := Fin 5 ⊕ Fin m
  let n := 5 + m
  let O := (n ^ (n - 1)) ^ n
  have hc : Fintype.card G = n := by simp [G,n]
  have hu : Nat.card (FORecoveryCompactness.Tables B G) ≤ 4 ^ n * O := by
    simpa only [hc] using hB G (by rw [hc]; dsimp [n]; omega)
  have hl : 5 ^ m * O ≤ Nat.card (FORecoveryCompactness.Tables Law3659 G) := retract_count 5 m
  have ho : 0 < O := by dsimp [O,n]; positivity
  have hratio : 5 ^ m ≤ K * 4 ^ n := by
    refine Nat.le_of_mul_le_mul_right (c := O) ?_ ho
    calc
      5 ^ m * O ≤ Nat.card (FORecoveryCompactness.Tables Law3659 G) := hl
      _ ≤ K * Nat.card (FORecoveryCompactness.Tables B G) := hK G
      _ ≤ K * (4 ^ n * O) := Nat.mul_le_mul_left K hu
      _ = _ := by ring
  have hnum := numerical_retract m
  have hnK : n ≤ 12500 * K := by
    refine Nat.le_of_mul_le_mul_right (c := 4 ^ n) ?_ (by positivity)
    calc
      n * 4 ^ n ≤ 12500 * 5 ^ m := hnum
      _ ≤ 12500 * (K * 4 ^ n) := Nat.mul_le_mul_left 12500 hratio
      _ = _ := by ring
  dsimp [n,m] at hnK
  omega

theorem retract_negative : ¬ Law3253.StructuralFrom Law3659 :=
  retract_negative_of_upper Law3253 (by
    intro G _ _ hn
    classical
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law3253.models_iff G ⟨f⟩))]
    exact EventualRowUpperCounting.upper_count_nat hn)


abbrev InvolutionCarrier (k : ℕ) := Fin k × (Fin 64 ⊕ Fin 64)

def involutionDiag (k : ℕ) (p : Fin k → Equiv.Perm (Fin 64)) :
    InvolutionCarrier k → InvolutionCarrier k
  | (t,.inl x) => (t,.inr (p t x))
  | (t,.inr y) => (t,.inl ((p t).symm y))

theorem involutionDiag_involutive (k : ℕ) (p : Fin k → Equiv.Perm (Fin 64))
    (x : InvolutionCarrier k) : involutionDiag k p (involutionDiag k p x) = x := by
  rcases x with ⟨t,x⟩
  cases x <;> simp [involutionDiag]

def involutionEncode (k : ℕ)
    (p : (Fin k → Equiv.Perm (Fin 64)) × OffTable (A := InvolutionCarrier k)) :
    FORecoveryCompactness.Tables Law151 (InvolutionCarrier k) :=
  ⟨operation (involutionDiag k p.1) p.2,
    (@Law151.models_iff _ ⟨operation (involutionDiag k p.1) p.2⟩).mpr
      (satisfies_151 _ _ (involutionDiag_involutive k p.1))⟩

theorem involutionEncode_injective (k : ℕ) : Function.Injective (involutionEncode k) := by
  intro p q h
  have he : (involutionDiag k p.1, p.2) = (involutionDiag k q.1, q.2) :=
    operation_injective (congrArg Subtype.val h)
  apply Prod.ext
  · funext t
    apply Equiv.ext
    intro x
    have hh := congrFun (congrArg Prod.fst he) (t, Sum.inl x)
    exact Sum.inr.inj (congrArg Prod.snd hh)
  · exact (Prod.mk.inj he).2

theorem involution_count (k : ℕ) :
    (Nat.factorial 64) ^ k * ((128 * k) ^ (128 * k - 1)) ^ (128 * k) ≤
      Nat.card (FORecoveryCompactness.Tables Law151 (InvolutionCarrier k)) := by
  have hh := Nat.card_le_card_of_injective (involutionEncode k) (involutionEncode_injective k)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    off_count,Fintype.card_perm,Fintype.card_sum,InvolutionCarrier,Nat.reduceAdd,Nat.mul_comm] using hh

theorem factorial_bound : 2 * 4 ^ 128 ≤ Nat.factorial 64 := by decide

theorem involution_negative_of_upper (B : NatMagmaLaw)
    (hB : ∀ (G : Type) [Fintype G] [Nonempty G], 3 ≤ Fintype.card G →
      Nat.card (FORecoveryCompactness.Tables B G) ≤ 4 ^ Fintype.card G *
        (Fintype.card G ^ (Fintype.card G - 1)) ^ Fintype.card G) :
    ¬ B.StructuralFrom Law151 := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts Law151 B h
  let k := K + 1
  let G := InvolutionCarrier k
  let n := 128 * k
  let O := (n ^ (n - 1)) ^ n
  letI : NeZero k := ⟨by dsimp [k]; omega⟩
  have hc : Fintype.card G = n := by simp [G,InvolutionCarrier,n,Nat.mul_comm]
  have hn : 3 ≤ n := by dsimp [n,k]; omega
  have hu : Nat.card (FORecoveryCompactness.Tables B G) ≤ 4 ^ n * O := by
    simpa only [hc] using hB G (by simpa only [hc] using hn)
  have hl : (Nat.factorial 64) ^ k * O ≤ Nat.card (FORecoveryCompactness.Tables Law151 G) :=
    involution_count k
  have ho : 0 < O := pow_pos (pow_pos (by omega) _) _
  have hratio : (Nat.factorial 64) ^ k ≤ K * 4 ^ n := by
    refine Nat.le_of_mul_le_mul_right (c := O) ?_ ho
    calc
      _ ≤ Nat.card (FORecoveryCompactness.Tables Law151 G) := hl
      _ ≤ K * Nat.card (FORecoveryCompactness.Tables B G) := hK G
      _ ≤ K * (4 ^ n * O) := Nat.mul_le_mul_left K hu
      _ = _ := by ring
  have hp : 2 ^ k * 4 ^ n ≤ (Nat.factorial 64) ^ k := by
    have hh := Nat.pow_le_pow_left factorial_bound k
    simpa only [mul_pow,← pow_mul] using hh
  have hbad : 2 ^ k ≤ K := Nat.le_of_mul_le_mul_right (hp.trans hratio) (by positivity)
  have hh : k < 2 ^ k := Nat.lt_two_pow_self
  dsimp [k] at hh hbad
  omega

theorem involution_negative : ¬ Law3253.StructuralFrom Law151 :=
  involution_negative_of_upper Law3253 (by
    intro G _ _ hn
    classical
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => @Law3253.models_iff G ⟨f⟩))]
    exact EventualRowUpperCounting.upper_count_nat hn)


end DiagonalTableCounting


theorem Equation3253_not_StructuralFrom_Equation3659_compactness :
    ¬ Law3253.StructuralFrom Law3659 := DiagonalTableCounting.retract_negative

/-- info: 'Equation3253_not_StructuralFrom_Equation3659_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3253_not_StructuralFrom_Equation3659_compactness


theorem Equation3253_not_StructuralFrom_Equation151_compactness :
    ¬ Law3253.StructuralFrom Law151 := DiagonalTableCounting.involution_negative

/-- info: 'Equation3253_not_StructuralFrom_Equation151_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3253_not_StructuralFrom_Equation151_compactness
