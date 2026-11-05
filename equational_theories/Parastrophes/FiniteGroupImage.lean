import equational_theories.Parastrophes.Catalogue
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! Identities valid in all finite cyclic groups hold in the two-element join
semilattice. Thus no single identity characterizes even the finite right-division
image of E543, which consists of abelian-group addition operations. -/
namespace Parastrophes
open Law FreeMagma

@[implicit_reducible] private def addNat : Magma Nat := ⟨(· + ·)⟩
@[implicit_reducible] private def addMod (n : Nat) : Magma (ZMod n) := ⟨(· + ·)⟩
@[implicit_reducible] private def joinBool : Magma Bool := ⟨(· || ·)⟩

private theorem eval_cast (n : Nat) (t : FreeMagma Nat) (v : Nat → Nat) :
    ((@evalInMagma _ _ addNat v t : Nat) : ZMod n) =
      @evalInMagma _ _ (addMod n) (fun i => (v i : ZMod n)) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change ((_ + _ : Nat) : ZMod n) = (_ + _)
    rw [Nat.cast_add, ha, hb]

/-- An identity of every finite cyclic group is an identity of natural addition:
choose a modulus larger than the two values being compared. -/
theorem natAddition_of_finiteCyclic {L : NatMagmaLaw}
    (h : ∀ n : Nat, 0 < n → @satisfies _ (ZMod n) (addMod n) L) :
    @satisfies _ Nat addNat L := by
  intro v
  let a := @evalInMagma _ _ addNat v L.lhs
  let b := @evalInMagma _ _ addNat v L.rhs
  let n := a + b + 1
  have hn : 0 < n := by omega
  have he := h n hn (fun i => (v i : ZMod n))
  have hc : (a : ZMod n) = (b : ZMod n) := by
    simpa only [a, b, eval_cast] using he
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_natCast_of_lt (by omega : a < n),
    ZMod.val_natCast_of_lt (by omega : b < n)] at hv
  exact hv

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

/-- Natural addition maps onto the two-element join semilattice by testing
whether a number is positive, so every additive identity holds there too. -/
theorem join_of_finiteCyclic {L : NatMagmaLaw}
    (h : ∀ n : Nat, 0 < n → @satisfies _ (ZMod n) (addMod n) L) :
    @satisfies _ Bool joinBool L := by
  intro v
  have hn := natAddition_of_finiteCyclic h (fun i => if v i then 1 else 0)
  have he := congrArg positive hn
  simpa only [eval_positive] using he

@[implicit_reducible] private def subMod (n : Nat) : Magma (ZMod n) := ⟨(· - ·)⟩

/-- If a source law holds of every finite cyclic subtraction magma, its right
image cannot be characterized by an identity. The image contains every finite
cyclic addition group but can never contain the two-element join semilattice. -/
theorem no_singleEquation_right_of_subtraction {L : NatMagmaLaw}
    (hs : ∀ n : Nat, 0 < n → @satisfies _ (ZMod n) (subMod n) L) :
    ¬ SingleEquation .fin L .right := by
  rintro ⟨target, ht⟩
  have hc : ∀ n : Nat, 0 < n → @satisfies _ (ZMod n) (addMod n) target := by
    intro n hn
    letI : NeZero n := ⟨by omega⟩
    apply (ht (ZMod n) (addMod n) (inferInstance : Finite (ZMod n))).mpr
    refine ⟨subMod n, hs n hn, ?_⟩
    constructor
    · intro x y
      change x + y - y = x
      exact add_sub_cancel_right x y
    · intro x y
      change x - y + y = x
      exact sub_add_cancel x y
  have hb := join_of_finiteCyclic hc
  have hQ := characterizes_sideQuasigroup ht Bool joinBool (inferInstance : Finite Bool) hb
  have he := (hQ true).1 (a₁ := false) (a₂ := true) rfl
  contradiction

namespace Catalogue

/-- Every finite cyclic subtraction group satisfies E543. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation543_fin :
    ¬ SingleEquation .fin Law543 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law543.models_iff _ (subMod n)).mpr
  intro x y z
  change x = (y - (z - (x - (y - z))))
  ring

/-- Every finite cyclic subtraction group satisfies E917. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation917_fin :
    ¬ SingleEquation .fin Law917 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law917.models_iff _ (subMod n)).mpr
  intro x y
  change x = (y - ((y - y) - (x - y)))
  ring

/-- Every finite cyclic subtraction group satisfies E978. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation978_fin :
    ¬ SingleEquation .fin Law978 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law978.models_iff _ (subMod n)).mpr
  intro x y z
  change x = (y - ((z - z) - (x - y)))
  ring

/-- Every finite cyclic subtraction group satisfies E1113. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation1113_fin :
    ¬ SingleEquation .fin Law1113 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law1113.models_iff _ (subMod n)).mpr
  intro x y
  change x = (y - ((y - (x - y)) - y))
  ring

/-- Every finite cyclic subtraction group satisfies E1117. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation1117_fin :
    ¬ SingleEquation .fin Law1117 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law1117.models_iff _ (subMod n)).mpr
  intro x y z
  change x = (y - ((y - (x - z)) - z))
  ring

/-- Every finite cyclic subtraction group satisfies E1152. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation1152_fin :
    ¬ SingleEquation .fin Law1152 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law1152.models_iff _ (subMod n)).mpr
  intro x y z
  change x = (y - ((z - (x - y)) - z))
  ring

/-- Every finite cyclic subtraction group satisfies E1658. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation1658_fin :
    ¬ SingleEquation .fin Law1658 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law1658.models_iff _ (subMod n)).mpr
  intro x y
  change x = ((x - y) - ((y - y) - y))
  ring

/-- Every finite cyclic subtraction group satisfies E1670. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation1670_fin :
    ¬ SingleEquation .fin Law1670 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law1670.models_iff _ (subMod n)).mpr
  intro x y z
  change x = ((x - y) - ((z - y) - z))
  ring

/-- Every finite cyclic subtraction group satisfies E1673. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation1673_fin :
    ¬ SingleEquation .fin Law1673 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law1673.models_iff _ (subMod n)).mpr
  intro x y z
  change x = ((x - y) - ((z - z) - y))
  ring

/-- Every finite cyclic subtraction group satisfies E1876. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation1876_fin :
    ¬ SingleEquation .fin Law1876 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law1876.models_iff _ (subMod n)).mpr
  intro x y z
  change x = ((x - (y - z)) - (z - y))
  ring

/-- Every finite cyclic subtraction group satisfies E2444. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation2444_fin :
    ¬ SingleEquation .fin Law2444 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law2444.models_iff _ (subMod n)).mpr
  intro x y
  change x = ((x - ((x - x) - y)) - y)
  ring

/-- Every finite cyclic subtraction group satisfies E2447. Its right image
therefore admits no single-equation characterization, even on finite carriers. -/
@[parastrophe_result] theorem right_noSingleEquation2447_fin :
    ¬ SingleEquation .fin Law2447 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law2447.models_iff _ (subMod n)).mpr
  intro x y
  change x = ((x - ((x - y) - x)) - y)
  ring

end Catalogue
end Parastrophes
