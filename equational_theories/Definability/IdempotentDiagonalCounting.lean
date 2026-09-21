import equational_theories.Definability.DiagonalTableCounting
import equational_theories.Definability.InvolutionCounting

/-!
# Idempotent diagonals outnumber involutive diagonals

On 4m points, maps fixing m distinguished points and sending all remaining
points into them supply m^(3m) idempotent diagonals. There are at most
2^(4m) (4m)^(2m) involutive diagonals. Off-diagonal entries are unrestricted
in either law. The unbounded count ratio refutes unrestricted FO-structural
interpretation from E3659 to E151.
-/

open Law Law.MagmaLaw
namespace IdempotentDiagonalCounting
variable {A : Type} [Fintype A] [DecidableEq A]
open DiagonalTableCounting

def tableEncode (f : FORecoveryCompactness.Tables Law151 A) :
    InvolutionCounting.Inv (A := A) × OffTable (A := A) :=
  (⟨fun x => f.val x x, fun x => ((@Law151.models_iff A ⟨f.val⟩).mp f.property x).symm⟩,
    fun x y => f.val x y.val)

omit [Fintype A] in
theorem tableEncode_injective : Function.Injective (tableEncode (A := A)) := by
  intro f g h
  have hh := congrArg (fun p : InvolutionCounting.Inv (A := A) × OffTable (A := A) =>
    operation p.1.val p.2) h
  apply Subtype.ext
  funext x y
  have he := congrFun (congrFun hh x) y
  by_cases hxy : y = x
  · subst y; simpa only [operation,tableEncode,dif_pos rfl] using he
  · simpa only [operation,tableEncode,dif_neg hxy] using he

theorem off_count_nat : Nat.card (OffTable (A := A)) =
    (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Nat.card_eq_fintype_card,off_count]

theorem upper_count [Nonempty A] : Nat.card (FORecoveryCompactness.Tables Law151 A) ≤
    (2 ^ Fintype.card A * Fintype.card A ^ (Fintype.card A / 2)) *
      (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  have hi : Nat.card (InvolutionCounting.Inv (A := A)) ≤
      2 ^ Fintype.card A * Fintype.card A ^ (Fintype.card A / 2) := by
    letI : LinearOrder A := LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective
    exact InvolutionCounting.upper_count
  calc
    _ ≤ Nat.card (InvolutionCounting.Inv (A := A) × OffTable (A := A)) :=
      Nat.card_le_card_of_injective tableEncode tableEncode_injective
    _ = Nat.card (InvolutionCounting.Inv (A := A)) *
        (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
      rw [Nat.card_prod,off_count_nat]
    _ ≤ _ := Nat.mul_le_mul_right _ hi

theorem coefficient (m : ℕ) :
    2 ^ (4 * m) * (4 * m) ^ (2 * m) = 256 ^ m * m ^ (2 * m) := by
  rw [mul_pow, pow_mul 2 4 m, pow_mul 4 2 m]
  norm_num
  rw [← Nat.mul_assoc,← mul_pow]
  norm_num

theorem power_split (m : ℕ) : m ^ (3 * m) = m ^ m * m ^ (2 * m) := by
  rw [show 3 * m = m + 2 * m by omega, pow_add]

theorem negative : ¬ Law151.StructuralFrom Law3659 := by
  intro h
  obtain ⟨K,hK⟩ := FORecoveryCompactness.bounded_counts Law3659 Law151 h
  let m := K + 512
  let G := Fin m ⊕ Fin (3 * m)
  let n := 4 * m
  let O := (n ^ (n - 1)) ^ n
  let Q := m ^ (2 * m) * O
  have hm : 512 ≤ m := by dsimp [m]; omega
  letI : NeZero m := ⟨by omega⟩
  have hc : Fintype.card G = n := by simp [G,n]; omega
  have hn : 0 < n := by dsimp [n]; omega
  have hhalf : n / 2 = 2 * m := by dsimp [n]; omega
  have ho : 0 < O := pow_pos (pow_pos hn _) _
  have hq : 0 < Q := Nat.mul_pos (pow_pos (by omega) _) ho
  have hu : Nat.card (FORecoveryCompactness.Tables Law151 G) ≤ 256 ^ m * Q := by
    have hh := upper_count (A := G)
    rw [hc,hhalf] at hh
    change Nat.card (FORecoveryCompactness.Tables Law151 G) ≤
      (2 ^ (4 * m) * (4 * m) ^ (2 * m)) * O at hh
    rw [coefficient] at hh
    simpa only [Q,Nat.mul_assoc] using hh
  have hl : m ^ m * Q ≤ Nat.card (FORecoveryCompactness.Tables Law3659 G) := by
    have hh := retract_count m (3 * m)
    have he : m + 3 * m = n := by dsimp [n]; omega
    rw [he] at hh
    have hp := power_split m
    rw [hp] at hh
    simpa only [Q,Nat.mul_assoc] using hh
  have hratio : m ^ m ≤ K * 256 ^ m := by
    refine Nat.le_of_mul_le_mul_right (c := Q) ?_ hq
    calc
      _ ≤ Nat.card (FORecoveryCompactness.Tables Law3659 G) := hl
      _ ≤ K * Nat.card (FORecoveryCompactness.Tables Law151 G) := hK G
      _ ≤ K * (256 ^ m * Q) := Nat.mul_le_mul_left K hu
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have hp : 2 ^ m * 256 ^ m ≤ m ^ m := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hm m
  have hbad : 2 ^ m ≤ K := Nat.le_of_mul_le_mul_right (hp.trans hratio) (by positivity)
  have hh : m < 2 ^ m := Nat.lt_two_pow_self
  dsimp [m] at hbad hh
  omega

end IdempotentDiagonalCounting

theorem Equation151_not_StructuralFrom_Equation3659_compactness :
    ¬ Law151.StructuralFrom Law3659 := IdempotentDiagonalCounting.negative

/-- info: 'Equation151_not_StructuralFrom_Equation3659_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation151_not_StructuralFrom_Equation3659_compactness
