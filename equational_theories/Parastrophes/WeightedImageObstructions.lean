import equational_theories.Parastrophes.FiniteGroupImage

/-! Finite weighted-addition images cannot be defined by an identity. Identities
pass from all finite cyclic reductions to natural numbers, then to Boolean join.
This obstructs the image even though its finite members all have the division. -/
namespace Parastrophes
open Law FreeMagma

@[implicit_reducible] private def weightedNat (k : Nat) : Magma Nat :=
  ⟨fun x y => k * x + y⟩
@[implicit_reducible] private def weightedMod (k n : Nat) : Magma (ZMod n) :=
  ⟨fun x y => k * x + y⟩
@[implicit_reducible] private def differenceMod (k n : Nat) : Magma (ZMod n) :=
  ⟨fun x y => y - k * x⟩
@[implicit_reducible] private def joinBool : Magma Bool := ⟨(· || ·)⟩

private theorem eval_cast (k n : Nat) (t : FreeMagma Nat) (v : Nat → Nat) :
    ((@evalInMagma _ _ (weightedNat k) v t : Nat) : ZMod n) =
      @evalInMagma _ _ (weightedMod k n) (fun i => (v i : ZMod n)) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change ((_ * _ + _ : Nat) : ZMod n) = (_ * _ + _)
    rw [Nat.cast_add, Nat.cast_mul, ha, hb]

private theorem natural_of_cyclic {k : Nat} {L : NatMagmaLaw}
    (h : ∀ n : Nat, 0 < n → @satisfies _ (ZMod n) (weightedMod k n) L) :
    @satisfies _ Nat (weightedNat k) L := by
  intro v
  let a := @evalInMagma _ _ (weightedNat k) v L.lhs
  let b := @evalInMagma _ _ (weightedNat k) v L.rhs
  let n := a + b + 1
  have he := h n (by omega) (fun i => (v i : ZMod n))
  have hc : (a : ZMod n) = (b : ZMod n) := by
    simpa only [a, b, eval_cast] using he
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_natCast_of_lt (by omega : a < n),
    ZMod.val_natCast_of_lt (by omega : b < n)] at hv
  exact hv

private def positive (n : Nat) : Bool := decide (n ≠ 0)

private theorem positive_weighted {k : Nat} (hk : 0 < k) (a b : Nat) :
    positive (k * a + b) = (positive a || positive b) := by
  cases k <;> cases a <;> cases b <;> simp_all [positive]

private theorem eval_positive {k : Nat} (hk : 0 < k)
    (t : FreeMagma Nat) (v : Nat → Bool) :
    positive (@evalInMagma _ _ (weightedNat k) (fun i => if v i then 1 else 0) t) =
      @evalInMagma _ _ joinBool v t := by
  induction t with
  | Leaf i => cases hv : v i <;> simp [evalInMagma, hv, positive]
  | Fork a b ha hb =>
    change positive (_ * _ + _) = (_ || _)
    rw [positive_weighted hk, ha, hb]

/-- If a source contains every cyclic model `x*y = y-k*x`, for positive k,
no single equation defines its finite left-division image `k*x+y`. -/
theorem no_singleEquation_left_of_weighted_difference {L : NatMagmaLaw} {k : Nat}
    (hk : 0 < k)
    (hs : ∀ n : Nat, 0 < n → @satisfies _ (ZMod n) (differenceMod k n) L) :
    ¬ SingleEquation .fin L .left := by
  rintro ⟨target, ht⟩
  have hc : ∀ n : Nat, 0 < n → @satisfies _ (ZMod n) (weightedMod k n) target := by
    intro n hn
    letI : NeZero n := ⟨by omega⟩
    apply (ht (ZMod n) (weightedMod k n) (inferInstance : Finite (ZMod n))).mpr
    refine ⟨differenceMod k n, hs n hn, ?_⟩
    constructor <;> intro x y
    · change k * x + y - k * x = y
      ring
    · change k * x + (y - k * x) = y
      ring
  have hb : @satisfies _ Bool joinBool target := by
    intro v
    have he := congrArg positive (natural_of_cyclic hc (fun i => if v i then 1 else 0))
    simpa only [eval_positive hk] using he
  have hQ := characterizes_sideQuasigroup ht Bool joinBool (inferInstance : Finite Bool) hb
  have he := (hQ true).1 (a₁ := false) (a₂ := true) rfl
  contradiction

namespace Catalogue

/-- E127 contains `x*y = y-2*x` at every finite cyclic order. Its left image
therefore has no single-equation characterization, even for finite carriers. -/
@[parastrophe_result] theorem left_noSingleEquation127_fin :
    ¬ SingleEquation .fin Law127 .left := by
  apply no_singleEquation_left_of_weighted_difference (k := 2) (by decide)
  intro n _
  apply (@Law127.models_iff _ (differenceMod 2 n)).mpr
  intro x y
  change x = (x - 2 * (y - 2*y)) - 2*y
  ring

/-- The weight-three family gives the analogous obstruction for E716. -/
@[parastrophe_result] theorem left_noSingleEquation716_fin :
    ¬ SingleEquation .fin Law716 .left := by
  apply no_singleEquation_left_of_weighted_difference (k := 3) (by decide)
  intro n _
  apply (@Law716.models_iff _ (differenceMod 3 n)).mpr
  intro x y
  change x = ((x - 3 * (y - 3*y)) - 3*y) - 3*y
  ring

/-- The right-bijectivity question for E870 is open, but its actual right
image already contains every cyclic addition group and cannot have one identity. -/
@[parastrophe_result] theorem right_noSingleEquation870_fin :
    ¬ SingleEquation .fin Law870 .right := by
  apply no_singleEquation_right_of_subtraction
  intro n _
  apply (@Law870.models_iff _ (⟨fun x y => x-y⟩ : Magma (ZMod n))).mpr
  intro x y
  change x = y - ((x-x) - (x-y))
  ring

end Catalogue
end Parastrophes
