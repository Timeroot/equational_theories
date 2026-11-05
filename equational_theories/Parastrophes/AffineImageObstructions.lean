import equational_theories.Parastrophes.FiniteGroupImage
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Obstructions from integer linear models and positive real evaluations.
Finite reductions force an identity on the integer model. A positive linear
evaluation then forces the same identity on Boolean join, which has no division.
This permits algebraic coefficients, represented by small integer matrices. -/
namespace Parastrophes.AffineImage
open Law FreeMagma

def reduce {d : Nat} (n : Nat) (x : Fin d → Int) : Fin d → ZMod n :=
  fun i => (x i : ZMod n)

private theorem int_eq_of_reductions {a b : Int}
    (h : ∀ n : Nat, 0 < n → (a : ZMod n) = (b : ZMod n)) : a = b := by
  let n := (b-a).natAbs + 1
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b n).mp (h n (by omega))
  have hz : b-a = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by
    rw [Int.natAbs_natCast]
    exact Nat.lt_succ_self _)
  omega

theorem integer_of_reductions {d : Nat} (D : Magma (Fin d → Int))
    (Dn : ∀ n : Nat, Magma (Fin d → ZMod n))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    {L : NatMagmaLaw}
    (h : ∀ n : Nat, 0 < n → @satisfies _ _ (Dn n) L) : @satisfies _ _ D L := by
  have he (n : Nat) (t : FreeMagma Nat) (v : Nat → Fin d → Int) :
      reduce n (@evalInMagma _ _ D v t) =
        @evalInMagma _ _ (Dn n) (fun i => reduce n (v i)) t := by
    induction t with
    | Leaf => rfl
    | Fork a b ha hb => exact (hc n _ _).trans (congrArg₂ (Dn n).op ha hb)
  intro v
  funext i
  apply int_eq_of_reductions
  intro n hn
  exact congrFun ((he n L.lhs v).trans ((h n hn _).trans (he n L.rhs v).symm)) i

@[implicit_reducible] private def joinBool : Magma Bool := ⟨(· || ·)⟩

theorem join_of_positive_evaluation {V : Type} (D : Magma V)
    (project : V → Real) (sample : Bool → V) {a b : Real}
    (ha : 0 < a) (hb : 0 < b)
    (hp : ∀ x y, project (D.op x y) = a * project x + b * project y)
    (h0 : project (sample false) = 0) (h1 : project (sample true) = 1)
    {L : NatMagmaLaw} (h : @satisfies _ _ D L) : @satisfies _ _ joinBool L := by
  have he (t : FreeMagma Nat) (v : Nat → Bool) :
      0 ≤ project (@evalInMagma _ _ D (fun i => sample (v i)) t) ∧
      (project (@evalInMagma _ _ D (fun i => sample (v i)) t) = 0 ↔
        @evalInMagma _ _ joinBool v t = false) := by
    induction t with
    | Leaf i => cases hv : v i <;> simp [evalInMagma, hv, h0, h1]
    | Fork x y hx hy =>
      change 0 ≤ project (D.op _ _) ∧ (project (D.op _ _) = 0 ↔ (_ || _) = false)
      rw [hp]
      constructor
      · exact add_nonneg (mul_nonneg ha.le hx.1) (mul_nonneg hb.le hy.1)
      · rw [add_eq_zero_iff_of_nonneg (mul_nonneg ha.le hx.1) (mul_nonneg hb.le hy.1)]
        simp [mul_eq_zero, ne_of_gt ha, ne_of_gt hb, hx.2, hy.2]
  intro v
  have hl := (he L.lhs v).2
  have hr := (he L.rhs v).2
  have hv := congrArg project (h (fun i => sample (v i)))
  change @evalInMagma _ _ joinBool v L.lhs = @evalInMagma _ _ joinBool v L.rhs
  cases hL : @evalInMagma _ _ joinBool v L.lhs <;>
    cases hR : @evalInMagma _ _ joinBool v L.rhs <;> simp_all

/-- A positive real image of an integral division family obstructs every
single-equation characterization, already on finite carriers. -/
theorem no_singleEquation_left {L : NatMagmaLaw} {d : Nat}
    (D : Magma (Fin d → Int)) (Dn : ∀ n : Nat, Magma (Fin d → ZMod n))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    (hm : ∀ n : Nat, 0 < n → InImage L .left (Dn n))
    (project : (Fin d → Int) → Real) (sample : Bool → Fin d → Int) {a b : Real}
    (ha : 0 < a) (hb : 0 < b)
    (hp : ∀ x y, project (D.op x y) = a * project x + b * project y)
    (h0 : project (sample false) = 0) (h1 : project (sample true) = 1) :
    ¬ SingleEquation .fin L .left := by
  rintro ⟨target, ht⟩
  have hi : @satisfies _ _ D target := integer_of_reductions D Dn hc (by
    intro n hn
    letI : NeZero n := ⟨by omega⟩
    exact (ht _ (Dn n) (inferInstance : Finite (Fin d → ZMod n))).mpr (hm n hn))
  have hj := join_of_positive_evaluation D project sample ha hb hp h0 h1 hi
  have hQ := characterizes_sideQuasigroup ht Bool joinBool (inferInstance : Finite Bool) hj
  have he := (hQ true).1 (a₁ := false) (a₂ := true) rfl
  contradiction

/-- It suffices to evaluate the source operation as `a*x+b*y`, with a negative
and b positive. The inverse identities force positive coefficients for division.
This avoids separately expanding a possibly complicated inverse matrix. -/
theorem no_singleEquation_left_of_source {L : NatMagmaLaw} {d : Nat}
    (M D : Magma (Fin d → Int)) (Dn : ∀ n : Nat, Magma (Fin d → ZMod n))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    (hm : ∀ n : Nat, 0 < n → InImage L .left (Dn n))
    (hd : IsDivision .left M D)
    (project : (Fin d → Int) → Real) (sample : Bool → Fin d → Int) {a b : Real}
    (ha : a < 0) (hb : 0 < b)
    (hp : ∀ x y, project (M.op x y) = a * project x + b * project y)
    (h0 : project (sample false) = 0) (h1 : project (sample true) = 1) :
    ¬ SingleEquation .fin L .left := by
  refine no_singleEquation_left D Dn hc hm project sample
    (a := -a/b) (b := 1/b) (div_pos (neg_pos.mpr ha) hb)
    (div_pos zero_lt_one hb) ?_ h0 h1
  intro x y
  have he := congrArg project (hd.1 x y)
  rw [hp] at he
  have hv : project (D.op x y) = (project y - a * project x) / b :=
    (eq_div_iff (ne_of_gt hb)).mpr (by linarith)
  rw [hv]
  ring

end Parastrophes.AffineImage
