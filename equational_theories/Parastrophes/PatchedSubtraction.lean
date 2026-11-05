import equational_theories.Parastrophes.FiniteGroupImage
import Mathlib.Tactic.Abel

/-!
# A nonlinear obstruction to division-image characterizations

On an abelian group, change the zero row of `y-x` to `-y`.
The resulting operation satisfies E1278, E1325 and E1387. Its left division
is `x+y` except in the zero row, where it is `-y`.
Every finite piece of positive natural addition is consequently reproduced
in a sufficiently large finite cyclic model. Identities pass to natural
addition, then to Boolean join, which has no left division.
-/
namespace Parastrophes.PatchedSubtraction
open Law FreeMagma

section Group
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

@[implicit_reducible] def source : Magma G :=
  ⟨fun x y => if x = 0 then -y else y - x⟩

@[implicit_reducible] def division : Magma G :=
  ⟨fun x y => if x = 0 then -y else x + y⟩

@[simp] theorem source_op (x y : G) :
    (source (G := G)).op x y = if x = 0 then -y else y - x := rfl

@[simp] theorem division_op (x y : G) :
    (division (G := G)).op x y = if x = 0 then -y else x + y := rfl

@[simp] theorem square (x : G) : (source (G := G)).op x x = 0 := by
  by_cases h : x = 0 <;> simp [h]

@[simp] theorem zero_row (y : G) : (source (G := G)).op 0 y = -y := by
  simp

theorem cancel (x y : G) :
    (source (G := G)).op x ((source (G := G)).op (-x) y) = y := by
  by_cases h : x = 0
  · subst x; simp
  · have hn : -x ≠ 0 := neg_ne_zero.mpr h
    simp only [source_op, if_neg h, if_neg hn]
    abel

theorem isDivision : IsDivision .left (source (G := G)) division := by
  constructor <;> intro x y <;> by_cases h : x = 0
  all_goals simp [h]

theorem equation1387 : @Equation1387 G source := by
  intro x y z
  simp only [square, zero_row]
  exact (cancel y x).symm

theorem equation1325 : @Equation1325 G source := by
  intro x y
  exact equation1387 x y y

theorem equation1278 : @Equation1278 G source := by
  intro x y
  simp only [square, zero_row]
  exact (cancel y x).symm

end Group

@[implicit_reducible] private def addNat : Magma Nat := ⟨(· + ·)⟩
@[implicit_reducible] private def joinBool : Magma Bool := ⟨(· || ·)⟩

private theorem eval_pos (t : FreeMagma Nat) (v : Nat → Nat) (hv : ∀ i, 0 < v i) :
    0 < @evalInMagma _ _ addNat v t := by
  induction t with
  | Leaf i => exact hv i
  | Fork a b ha hb => exact Nat.add_pos_left ha _

/-- A positive additive term and all its subterms avoid the patched zero row
when the modulus is larger than its value. -/
private theorem eval_mod (t : FreeMagma Nat) (v : Nat → Nat) (hv : ∀ i, 0 < v i)
    (n : Nat) (hn : @evalInMagma _ _ addNat v t < n) :
    ((@evalInMagma _ _ addNat v t : Nat) : ZMod n) =
      @evalInMagma _ _ (division (G := ZMod n)) (fun i => (v i : ZMod n)) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    let av := @evalInMagma _ _ addNat v a
    let bv := @evalInMagma _ _ addNat v b
    change av + bv < n at hn
    have hza : (av : ZMod n) ≠ 0 := by
      intro he
      have hh := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (by omega : av < n), ZMod.val_zero] at hh
      have hp : 0 < av := eval_pos a v hv
      omega
    change ((av + bv : Nat) : ZMod n) = (division (G := ZMod n)).op _ _
    rw [← ha (by omega), ← hb (by omega)]
    change ((av + bv : Nat) : ZMod n) = if (av : ZMod n) = 0 then -(bv : ZMod n)
      else (av : ZMod n) + (bv : ZMod n)
    simp only [if_neg hza, Nat.cast_add]

private theorem positive_addition_of_finite {L : NatMagmaLaw}
    (h : ∀ n : Nat, 0 < n → @satisfies _ _ (division (G := ZMod n)) L)
    (v : Nat → Nat) (hv : ∀ i, 0 < v i) :
    @evalInMagma _ _ addNat v L.lhs = @evalInMagma _ _ addNat v L.rhs := by
  let a := @evalInMagma _ _ addNat v L.lhs
  let b := @evalInMagma _ _ addNat v L.rhs
  let n := a + b + 1
  have he := h n (by omega) (fun i => (v i : ZMod n))
  have hc : (a : ZMod n) = (b : ZMod n) :=
    (eval_mod L.lhs v hv n (by omega)).trans
      (he.trans (eval_mod L.rhs v hv n (by omega)).symm)
  have hh := congrArg ZMod.val hc
  rw [ZMod.val_natCast_of_lt (by omega : a < n),
    ZMod.val_natCast_of_lt (by omega : b < n)] at hh
  exact hh

private theorem eval_add (t : FreeMagma Nat) (v w : Nat → Nat) :
    @evalInMagma _ _ addNat (fun i => v i + w i) t =
      @evalInMagma _ _ addNat v t + @evalInMagma _ _ addNat w t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change _ + _ = (_ + _) + (_ + _)
    rw [ha, hb]
    omega

/-- Shifting every variable by one removes positivity restrictions.
Evaluation at all ones supplies the common shift to cancel. -/
private theorem addition_of_finite {L : NatMagmaLaw}
    (h : ∀ n : Nat, 0 < n → @satisfies _ _ (division (G := ZMod n)) L) :
    @satisfies _ Nat addNat L := by
  intro v
  have h1 := positive_addition_of_finite h (fun _ => 1) (fun _ => Nat.zero_lt_one)
  have h2 := positive_addition_of_finite h (fun i => v i + 1) (fun i => Nat.zero_lt_succ (v i))
  rw [eval_add L.lhs v (fun _ => 1), eval_add L.rhs v (fun _ => 1), h1] at h2
  exact Nat.add_right_cancel h2

private def positive (n : Nat) : Bool := decide (n ≠ 0)

private theorem positive_add (a b : Nat) : positive (a + b) = (positive a || positive b) := by
  cases a <;> cases b <;> simp [positive]

private theorem eval_positive (t : FreeMagma Nat) (v : Nat → Bool) :
    positive (@evalInMagma _ _ addNat (fun i => if v i then 1 else 0) t) =
      @evalInMagma _ _ joinBool v t := by
  induction t with
  | Leaf i => cases hv : v i <;> simp [evalInMagma, hv, positive]
  | Fork a b ha hb =>
    change positive (_ + _) = (_ || _)
    rw [positive_add, ha, hb]

/-- Every identity of these finite division operations holds in Boolean join. -/
theorem join_of_finite {L : NatMagmaLaw}
    (h : ∀ n : Nat, 0 < n → @satisfies _ _ (division (G := ZMod n)) L) :
    @satisfies _ Bool joinBool L := by
  intro v
  have he := congrArg positive (addition_of_finite h (fun i => if v i then 1 else 0))
  simpa only [eval_positive] using he

/-- A law containing this patched subtraction family cannot have a
single-equation finite left-division image. -/
theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ n : Nat, 0 < n → @satisfies _ _ (source (G := ZMod n)) L) :
    ¬ SingleEquation .fin L .left := by
  rintro ⟨target, ht⟩
  have hc : ∀ n : Nat, 0 < n → @satisfies _ _ (division (G := ZMod n)) target := by
    intro n hn
    letI : NeZero n := ⟨by omega⟩
    exact (ht (ZMod n) division (inferInstance : Finite (ZMod n))).mpr
      ⟨source, hL n hn, isDivision⟩
  have hQ := characterizes_sideQuasigroup ht Bool joinBool
    (inferInstance : Finite Bool) (join_of_finite hc)
  have he := (hQ true).1 (a₁ := false) (a₂ := true) rfl
  contradiction

end Parastrophes.PatchedSubtraction

namespace Parastrophes.Catalogue
open Law

/-- Patched cyclic subtraction obstructs every defining identity for
E1278's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation1278_fin :
    ¬ SingleEquation .fin Law1278 .left := by
  apply PatchedSubtraction.obstruction
  intro n _
  exact (@Law1278.models_iff (ZMod n) (PatchedSubtraction.source (G := ZMod n))).mpr
    PatchedSubtraction.equation1278

/-- E1325's finite left-division image has no single defining equation. -/
@[parastrophe_result] theorem left_noSingleEquation1325_fin :
    ¬ SingleEquation .fin Law1325 .left := by
  apply PatchedSubtraction.obstruction
  intro n _
  exact (@Law1325.models_iff (ZMod n) (PatchedSubtraction.source (G := ZMod n))).mpr
    PatchedSubtraction.equation1325

/-- E1387's finite left-division image has no single defining equation. -/
@[parastrophe_result] theorem left_noSingleEquation1387_fin :
    ¬ SingleEquation .fin Law1387 .left := by
  apply PatchedSubtraction.obstruction
  intro n _
  exact (@Law1387.models_iff (ZMod n) (PatchedSubtraction.source (G := ZMod n))).mpr
    PatchedSubtraction.equation1387

end Parastrophes.Catalogue
