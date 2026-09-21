import equational_theories.Definability.Basic
import equational_theories.Equations.All
import Mathlib.Tactic.Group

/-!
E3342/E3545 mutual term recovery on `Option (I × A)`, for any group `A`,
a central distinguished element `e`, and a successor map on `I` without
cycles of length one or two. No injectivity or finiteness is assumed.

The 10-leaf forward and 16-leaf backward terms work on finite cycles and
infinite chains alike. This is a family result, not a general board implication.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace SuccessorFiber
variable {I A : Type} [DecidableEq I] [Group A]
variable (s : I → I) (h₁ : ∀ i, s i ≠ i) (h₂ : ∀ i, s (s i) ≠ i)

@[implicit_reducible] def source (e : A) : Magma (Option (I × A)) where
  op x y := match x, y with
    | some (i,u), some (j,v) =>
      if i = j then some (s i, 1)
      else if s i = j then some (i, u * v⁻¹ * e)
      else if i = s j then some (j, v * u⁻¹)
      else none
    | _, _ => none

@[implicit_reducible] def target (e : A) : Magma (Option (I × A)) where
  op x y := match x, y with
    | some (i,u), some (j,v) =>
      if i = j then some (s i, 1)
      else if s i = j then some (i, u * v⁻¹ * e * e)
      else if i = s j then some (j, v * u⁻¹ * e)
      else none
    | _, _ => none

@[simp] theorem source_none_left (e : A) (x) : (source s e).op none x = none := by cases x <;> rfl
@[simp] theorem source_none_right (e : A) (x) : (source s e).op x none = none := by cases x <;> rfl
@[simp] theorem target_none_left (e : A) (x) : (target s e).op none x = none := by cases x <;> rfl
@[simp] theorem target_none_right (e : A) (x) : (target s e).op x none = none := by cases x <;> rfl

@[simp] theorem source_same (e u v : A) (i : I) :
    (source s e).op (some (i,u)) (some (i,v)) = some (s i,1) := by simp [Magma.op]
include h₁ in
@[simp] theorem source_next (e u v : A) (i : I) :
    (source s e).op (some (i,u)) (some (s i,v)) = some (i,u*v⁻¹*e) := by
  simp [Magma.op, Ne.symm (h₁ i)]
include h₁ h₂ in
@[simp] theorem source_prev (e u v : A) (i : I) :
    (source s e).op (some (s i,u)) (some (i,v)) = some (i,v*u⁻¹) := by
  simp [Magma.op, h₁ i, h₂ i]
@[simp] theorem target_same (e u v : A) (i : I) :
    (target s e).op (some (i,u)) (some (i,v)) = some (s i,1) := by simp [Magma.op]
include h₁ in
@[simp] theorem target_next (e u v : A) (i : I) :
    (target s e).op (some (i,u)) (some (s i,v)) = some (i,u*v⁻¹*e*e) := by
  simp [Magma.op, Ne.symm (h₁ i)]
include h₁ h₂ in
@[simp] theorem target_prev (e u v : A) (i : I) :
    (target s e).op (some (s i,u)) (some (i,v)) = some (i,v*u⁻¹*e) := by
  simp [Magma.op, h₁ i, h₂ i]

variable (e : A) (he : ∀ a : A, e*a = a*e)

include h₁ h₂ he in
theorem source_law : @Equation3342 (Option (I × A)) (source s e) := by
  intro x y
  cases x with
  | none => simp
  | some x =>
    obtain ⟨i, u⟩ := x
    cases y with
    | none => simp
    | some y =>
      obtain ⟨j, v⟩ := y
      simp only [source_same, source_next s h₁, mul_one, inv_one]
      by_cases hij : i = j
      · subst j; simp
      by_cases hn : s i = j
      · subst j
        simp only [source_next s h₁, source_prev s h₁ h₂, Option.some.injEq, Prod.mk.injEq, true_and]
        group
        have hv : Commute e (v ^ (-1 : ℤ)) := he _
        simp only [mul_assoc, hv.eq]
      by_cases hp : s j = i
      · subst i
        simp only [source_prev s h₁ h₂, source_next s h₁, Option.some.injEq, Prod.mk.injEq, true_and]
        group
        have hu : Commute e (u ^ (-1 : ℤ)) := he _
        simp only [mul_assoc, (hu.zpow_left (-1)).eq]
        group
      · simp [Magma.op, hij, Ne.symm hij, hn, Ne.symm hn, hp, Ne.symm hp]

include h₁ h₂ he in
theorem target_law : @Equation3545 (Option (I × A)) (target s e) := by
  intro x y
  cases x with
  | none => simp
  | some x =>
    obtain ⟨i, u⟩ := x
    cases y with
    | none => simp
    | some y =>
      obtain ⟨j, v⟩ := y
      simp only [target_same, target_prev s h₁ h₂, mul_one, inv_one]
      by_cases hij : i = j
      · subst j; simp
      by_cases hn : s i = j
      · subst j
        simp only [target_next s h₁, target_prev s h₁ h₂, Option.some.injEq, Prod.mk.injEq, true_and]
        group
        have hv : Commute e (v ^ (-1 : ℤ)) := he _
        simp only [mul_assoc, hv.eq]
      by_cases hp : s j = i
      · subst i
        simp only [target_prev s h₁ h₂, target_next s h₁, Option.some.injEq, Prod.mk.injEq, true_and]
        group
        have hu : Commute e (u ^ (-1 : ℤ)) := he _
        simp only [mul_assoc, (hu.zpow_left (-1)).eq]
        group
      · simp [Magma.op, hij, Ne.symm hij, hn, Ne.symm hn, hp, Ne.symm hp]

def forward (x y : Option (I × A)) := ((source s e).op ((source s e).op ((source s e).op ((source s e).op x y) x) ((source s e).op x y)) ((source s e).op ((source s e).op ((source s e).op x y) y) ((source s e).op y x)))
include h₁ h₂ in
theorem forward_eq (x y : Option (I × A)) : forward s e x y = (target s e).op x y := by
  cases x with
  | none => simp [forward]
  | some x =>
    obtain ⟨i, u⟩ := x
    cases y with
    | none => simp [forward]
    | some y =>
      obtain ⟨j, v⟩ := y
      by_cases hij : i = j
      · subst j
        simp [forward, source_next s h₁, source_prev s h₁ h₂]
      by_cases hn : s i = j
      · subst j
        simp [forward, source_next s h₁, source_prev s h₁ h₂,
          target_next s h₁]
      by_cases hp : s j = i
      · subst i
        simp [forward, source_next s h₁, source_prev s h₁ h₂,
          target_prev s h₁ h₂]
      · simp [forward, Magma.op, hij, hn, Ne.symm hp]
def backward (x y : Option (I × A)) := ((target s e).op ((target s e).op ((target s e).op ((target s e).op x ((target s e).op x x)) ((target s e).op x x)) ((target s e).op ((target s e).op ((target s e).op y x) y) y)) ((target s e).op ((target s e).op y ((target s e).op y y)) ((target s e).op ((target s e).op ((target s e).op y x) x) x)))
include h₁ h₂ he in
theorem backward_eq (x y : Option (I × A)) : backward s e x y = (source s e).op x y := by
  cases x with
  | none => simp [backward]
  | some x =>
    obtain ⟨i, u⟩ := x
    cases y with
    | none => simp [backward]
    | some y =>
      obtain ⟨j, v⟩ := y
      by_cases hij : i = j
      · subst j
        simp [backward,
          target_next s h₁, target_prev s h₁ h₂]
      by_cases hn : s i = j
      · subst j
        simp [backward, source_next s h₁,
          target_next s h₁, target_prev s h₁ h₂]
        group
        have hv : Commute e (v ^ (-1 : ℤ)) := he _
        simp only [mul_assoc, (hv.zpow_left (-1)).eq]
        group
      by_cases hp : s j = i
      · subst i
        simp [backward, source_prev s h₁ h₂,
          target_next s h₁, target_prev s h₁ h₂]
        group
        have hu : Commute e (u ^ (-1 : ℤ)) := he _
        simp only [mul_assoc, (hu.zpow_left (-3)).eq]
        group
      · have ht : (target s e).op (some (j,v)) (some (i,u)) = none := by
          simp [Magma.op, Ne.symm hij, hp, Ne.symm hn]
        simp only [backward, ht, target_none_left, target_none_right]
        simp [Magma.op, hij, hn, Ne.symm hp]

open FirstOrder.Language
private abbrev tm (a b : (MagmaLanguage.withConstants (∅ : Set (Option (I × A)))).Term (Fin 2)) :
    (MagmaLanguage.withConstants (∅ : Set (Option (I × A)))).Term (Fin 2) :=
  Functions.apply₂ (Sum.inl ()) a b
include h₁ h₂ he in
/-- Uniform mutual recovery on this successor family, without a finiteness hypothesis. -/
theorem termStructural3545 : Law3545.TermStructuralOnMagma (source s e) := by
  refine ⟨target s e, ?_, ?_, ?_⟩
  · rw [@Law3545.models_iff]
    exact target_law s h₁ h₂ e he
  · refine ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (tm (Term.var 0) (Term.var 1))) (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (tm (Term.var 1) (Term.var 0)))), ?_⟩
    funext v
    change (target s e).op (v 0) (v 1) = forward s e (v 0) (v 1)
    exact (forward_eq s h₁ h₂ e _ _).symm
  · refine ⟨(tm (tm (tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 0) (Term.var 0))) (tm (tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)) (Term.var 1))) (tm (tm (Term.var 1) (tm (Term.var 1) (Term.var 1))) (tm (tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)) (Term.var 0)))), ?_⟩
    funext v
    change (source s e).op (v 0) (v 1) = backward s e (v 0) (v 1)
    exact (backward_eq s h₁ h₂ e he _ _).symm

include h₁ h₂ he in
/-- Uniform mutual recovery on this successor family, without a finiteness hypothesis. -/
theorem termStructural3342 : Law3342.TermStructuralOnMagma (target s e) := by
  refine ⟨source s e, ?_, ?_, ?_⟩
  · rw [@Law3342.models_iff]
    exact source_law s h₁ h₂ e he
  · refine ⟨(tm (tm (tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 0) (Term.var 0))) (tm (tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)) (Term.var 1))) (tm (tm (Term.var 1) (tm (Term.var 1) (Term.var 1))) (tm (tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)) (Term.var 0)))), ?_⟩
    funext v
    change (source s e).op (v 0) (v 1) = backward s e (v 0) (v 1)
    exact (backward_eq s h₁ h₂ e he _ _).symm
  · refine ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (tm (Term.var 0) (Term.var 1))) (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (tm (Term.var 1) (Term.var 0)))), ?_⟩
    funext v
    change (target s e).op (v 0) (v 1) = forward s e (v 0) (v 1)
    exact (forward_eq s h₁ h₂ e _ _).symm

/-- info: 'SuccessorFiber.source_law' depends on axioms: [propext] -/
#guard_msgs in
#print axioms source_law
/-- info: 'SuccessorFiber.target_law' depends on axioms: [propext] -/
#guard_msgs in
#print axioms target_law
/-- info: 'SuccessorFiber.termStructural3545' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms termStructural3545
/-- info: 'SuccessorFiber.termStructural3342' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms termStructural3342
end SuccessorFiber
