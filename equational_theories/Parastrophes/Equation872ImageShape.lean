import equational_theories.Parastrophes.Equation872ImageBasis
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# A necessary shape for E872's finite division-image identity

If `x_i = t` characterizes this image, the rightmost variable of `t` is `x_i`
and its rightmost branch has exactly three operations. Right projection forces
the variable, the three-cycle forces the depth to be a multiple of three, and
the cycle of length equal to that depth forces it to divide three.
-/
namespace Parastrophes.Eq872ImageShape
open Law FreeMagma

def rightmost : FreeMagma Nat → Nat
  | .Leaf i => i
  | .Fork _ b => rightmost b

def rightDepth : FreeMagma Nat → Nat
  | .Leaf _ => 0
  | .Fork _ b => rightDepth b + 1

@[implicit_reducible] def rightProjection (G : Type) : Magma G := ⟨fun _ y => y⟩

private theorem eval_projection {G : Type} (t : FreeMagma Nat) (v : Nat → G) :
    @evalInMagma _ G (rightProjection G) v t = v (rightmost t) := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb => exact hb

@[implicit_reducible] def shift (n : Nat) : Magma (ZMod n) := ⟨fun _ y => y+1⟩
@[implicit_reducible] def unshift (n : Nat) : Magma (ZMod n) := ⟨fun _ y => y-1⟩

theorem shift_division (n : Nat) : IsDivision .left (unshift n) (shift n) := by
  constructor
  · intro x y; change (y+1)-1=y; simp
  · intro x y; change (y-1)+1=y; simp

theorem unshift_law_iff (n : Nat) : @Equation872 (ZMod n) (unshift n) ↔ (3 : ZMod n)=0 := by
  constructor
  · intro h
    have he := h 0 0
    change (0 : ZMod n) = ((0-1)-1)-1 at he
    linear_combination he
  · intro h x y
    change x = ((x-1)-1)-1
    linear_combination h

theorem eval_shift (n : Nat) (t : FreeMagma Nat) (v : Nat → ZMod n) :
    @evalInMagma _ _ (shift n) v t = v (rightmost t) + (rightDepth t : ZMod n) := by
  induction t with
  | Leaf => simp [evalInMagma, rightmost, rightDepth]
  | Fork a b ha hb =>
    change @evalInMagma _ _ (shift n) v b + 1 = _
    rw [hb]
    simp [rightmost, rightDepth, add_assoc]

theorem rightmost_eq {i : Nat} {t : FreeMagma Nat}
    (h : Characterizes .fin Law872 .left ⟨.Leaf i,t⟩) : rightmost t = i := by
  have hp : @satisfies _ Bool (rightProjection Bool) (⟨.Leaf i,t⟩ : NatMagmaLaw) := by
    apply (h Bool _ (inferInstance : Finite Bool)).mpr
    exact ⟨rightProjection Bool, (@Law872.models_iff Bool (rightProjection Bool)).mpr (fun _ _ => rfl),
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  have he := hp (fun j => decide (j=i))
  change decide (i=i) = @evalInMagma _ Bool (rightProjection Bool) _ t at he
  rw [eval_projection] at he
  exact of_decide_eq_true (he.symm.trans (by simp))

/-- A single candidate must retain the original three-step right branch;
longer such branches always admit an explicit bad cyclic model. -/
theorem rightDepth_eq_three {i : Nat} {t : FreeMagma Nat}
    (h : Characterizes .fin Law872 .left ⟨.Leaf i,t⟩) : rightDepth t = 3 := by
  have hr := rightmost_eq h
  have hd : rightDepth t ≠ 0 := by
    intro he
    cases t with
    | Leaf j =>
      change j=i at hr
      subst j
      let Z : Magma Bool := ⟨fun _ _ => false⟩
      have hz : @satisfies _ Bool Z (⟨.Leaf i,.Leaf i⟩ : NatMagmaLaw) := fun _ => rfl
      have hq := characterizes_sideQuasigroup h Bool Z (inferInstance : Finite Bool) hz
      have bad := (hq false).1 (a₁ := false) (a₂ := true) rfl
      contradiction
    | Fork a b => simp [rightDepth] at he
  have hthree : 3 ∣ rightDepth t := by
    have hp : @satisfies _ _ (shift 3) (⟨.Leaf i,t⟩ : NatMagmaLaw) := by
      apply (h _ _ (inferInstance : Finite (ZMod 3))).mpr
      refine ⟨unshift 3, (@Law872.models_iff (ZMod 3) (unshift 3)).mpr ?_, shift_division 3⟩
      exact (unshift_law_iff 3).mpr (by decide)
    have he := hp (fun _ => 0)
    change (0 : ZMod 3) = @evalInMagma _ _ (shift 3) _ t at he
    rw [eval_shift, zero_add] at he
    exact (ZMod.natCast_eq_zero_iff _ _).mp he.symm
  have hdepth : rightDepth t ∣ 3 := by
    let n := rightDepth t
    letI : NeZero n := ⟨hd⟩
    have hp : @satisfies _ _ (shift n) (⟨.Leaf i,t⟩ : NatMagmaLaw) := by
      intro v
      change v i = @evalInMagma _ _ (shift n) v t
      rw [eval_shift, hr]
      change v i = v i + (n : ZMod n)
      simp
    obtain ⟨M, hM, hm⟩ := (h _ _ (inferInstance : Finite (ZMod n))).mp hp
    have he : M = unshift n := division_unique (division_symm hm) (division_symm (shift_division n))
    have hM' := (@Law872.models_iff (ZMod n) M).mp hM
    rw [he] at hM'
    have hz := (unshift_law_iff n).mp hM'
    exact (ZMod.natCast_eq_zero_iff 3 n).mp hz
  exact Nat.dvd_antisymm hdepth hthree

/-- Both sides cannot be composite: every such identity admits the two-element
constant magma. Thus the depth restriction applies to every exact image law,
not only to candidates chosen in advance to have a variable on one side. -/
theorem target_shape {L : NatMagmaLaw} (h : Characterizes .fin Law872 .left L) :
    ∃ i t, (L = ⟨.Leaf i,t⟩ ∨ L = ⟨t,.Leaf i⟩) ∧
      rightmost t = i ∧ rightDepth t = 3 := by
  rcases L with ⟨a,b⟩
  cases a with
  | Leaf i => exact ⟨i,b,Or.inl rfl,rightmost_eq h,rightDepth_eq_three h⟩
  | Fork a₁ a₂ =>
    cases b with
    | Leaf i =>
      have hs : Characterizes .fin Law872 .left ⟨.Leaf i,.Fork a₁ a₂⟩ := by
        intro G D hG
        constructor
        · intro ht
          exact (h G D hG).mp (fun v => (ht v).symm)
        · intro hi v
          exact ((h G D hG).mpr hi v).symm
      exact ⟨i,.Fork a₁ a₂,Or.inr rfl,rightmost_eq hs,rightDepth_eq_three hs⟩
    | Fork b₁ b₂ =>
      let Z : Magma Bool := ⟨fun _ _ => false⟩
      have hz : @satisfies _ Bool Z (⟨.Fork a₁ a₂,.Fork b₁ b₂⟩ : NatMagmaLaw) :=
        fun _ => rfl
      have hq := characterizes_sideQuasigroup h Bool Z (inferInstance : Finite Bool) hz
      have bad := (hq false).1 (a₁ := false) (a₂ := true) rfl
      contradiction

/-- A finite-only consequence useful in testing stronger candidates. If the
inverse of row `y` factors pointwise through row `T y`, then the rows indexed
by `T` cover all rows. Elements with identical rows need not themselves agree. -/
theorem row_predecessor {G : Type} [Finite G] (D : Magma G) (A T : G → G)
    (hq : IsSideQuasigroup .left D)
    (h : ∀ x y, x = D.op y (D.op (A x) (D.op (T y) x))) :
    ∀ a, ∃ b, ∀ x, D.op (T b) x = D.op a x := by
  classical
  let R := Set.range D.op
  let row : G → R := fun y => ⟨D.op y, ⟨y,rfl⟩⟩
  let rep : R → G := fun q => Classical.choose q.property
  have rep_spec (q : R) : D.op (rep q) = q.val := Classical.choose_spec q.property
  let F : R → R := fun q => row (T (rep q))
  have hi : Function.Injective F := by
    intro a b he
    have ht : D.op (T (rep a)) = D.op (T (rep b)) := congrArg Subtype.val he
    apply Subtype.ext
    change a.val = b.val
    rw [← rep_spec a, ← rep_spec b]
    funext z
    let x := D.op (rep a) z
    have hz : D.op (A x) (D.op (T (rep a)) x) = z :=
      ((hq (rep a)).1 (h x (rep a))).symm
    have hb := h x (rep b)
    rw [← ht, hz] at hb
    exact hb
  have hs := Finite.surjective_of_injective hi
  intro a
  obtain ⟨q,hq⟩ := hs (row a)
  exact ⟨rep q, fun x => congrFun (congrArg Subtype.val hq) x⟩

end Parastrophes.Eq872ImageShape
