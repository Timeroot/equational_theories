import equational_theories.Definability.Basic
import equational_theories.Equations.All
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
/-!
E3342/E3545 mutual term recovery on `Fin 3 × A`, for any group `A` and
central distinguished element `e`. This extends the additive commutative family
in `check_definability_fiber_recovery.lean`; `A` can be infinite and noncommutative.
The forward and backward terms have 10 and 16 leaves. This is a family theorem,
not a general definability-board implication in either direction.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace NonabelianFiber

variable {A : Type} [Group A]
def base : Fin 3 → Fin 3 → Fin 3 := ![![1, 0, 2], ![0, 2, 1], ![2, 1, 0]]
def delta : Fin 3 → Fin 3 → Fin 3 := ![![0, 1, 2], ![2, 0, 1], ![1, 2, 0]]
@[implicit_reducible] def source (e : A) : Magma (Fin 3 × A) where
  op x y := (base x.1 y.1, if delta x.1 y.1 = 0 then 1 else if delta x.1 y.1 = 1 then x.2 * y.2⁻¹ * e else y.2 * x.2⁻¹)
@[implicit_reducible] def target (e : A) : Magma (Fin 3 × A) where
  op x y := (base x.1 y.1, if delta x.1 y.1 = 0 then 1 else if delta x.1 y.1 = 1 then x.2 * y.2⁻¹ * e * e else y.2 * x.2⁻¹ * e)
@[simp] theorem source_00 (e u v : A) : (source e).op (0, u) (0, v) = (1, 1) := rfl
@[simp] theorem source_01 (e u v : A) : (source e).op (0, u) (1, v) = (0, u * v⁻¹ * e) := rfl
@[simp] theorem source_02 (e u v : A) : (source e).op (0, u) (2, v) = (2, v * u⁻¹) := rfl
@[simp] theorem source_10 (e u v : A) : (source e).op (1, u) (0, v) = (0, v * u⁻¹) := rfl
@[simp] theorem source_11 (e u v : A) : (source e).op (1, u) (1, v) = (2, 1) := rfl
@[simp] theorem source_12 (e u v : A) : (source e).op (1, u) (2, v) = (1, u * v⁻¹ * e) := rfl
@[simp] theorem source_20 (e u v : A) : (source e).op (2, u) (0, v) = (2, u * v⁻¹ * e) := rfl
@[simp] theorem source_21 (e u v : A) : (source e).op (2, u) (1, v) = (1, v * u⁻¹) := rfl
@[simp] theorem source_22 (e u v : A) : (source e).op (2, u) (2, v) = (0, 1) := rfl
@[simp] theorem target_00 (e u v : A) : (target e).op (0, u) (0, v) = (1, 1) := rfl
@[simp] theorem target_01 (e u v : A) : (target e).op (0, u) (1, v) = (0, u * v⁻¹ * e * e) := rfl
@[simp] theorem target_02 (e u v : A) : (target e).op (0, u) (2, v) = (2, v * u⁻¹ * e) := rfl
@[simp] theorem target_10 (e u v : A) : (target e).op (1, u) (0, v) = (0, v * u⁻¹ * e) := rfl
@[simp] theorem target_11 (e u v : A) : (target e).op (1, u) (1, v) = (2, 1) := rfl
@[simp] theorem target_12 (e u v : A) : (target e).op (1, u) (2, v) = (1, u * v⁻¹ * e * e) := rfl
@[simp] theorem target_20 (e u v : A) : (target e).op (2, u) (0, v) = (2, u * v⁻¹ * e * e) := rfl
@[simp] theorem target_21 (e u v : A) : (target e).op (2, u) (1, v) = (1, v * u⁻¹ * e) := rfl
@[simp] theorem target_22 (e u v : A) : (target e).op (2, u) (2, v) = (0, 1) := rfl
theorem source_law (e : A) (he : ∀ a : A, e * a = a * e) : @Equation3342 (Fin 3 × A) (source e) := by
  intro ⟨a, u⟩ ⟨b, v⟩
  fin_cases a <;> fin_cases b <;> simp <;> group
  all_goals
    have hu : Commute e (u ^ (-1 : ℤ)) := he _
    have hv : Commute e (v ^ (-1 : ℤ)) := he _
    simp only [mul_assoc, hv.eq, (hu.zpow_left (-1)).eq]
    group
theorem target_law (e : A) (he : ∀ a : A, e * a = a * e) : @Equation3545 (Fin 3 × A) (target e) := by
  intro ⟨a, u⟩ ⟨b, v⟩
  fin_cases a <;> fin_cases b <;> simp <;> group
  all_goals
    have hu : Commute e (u ^ (-1 : ℤ)) := he _
    have hv : Commute e (v ^ (-1 : ℤ)) := he _
    simp only [mul_assoc, hv.eq, (hu.zpow_left (-1)).eq]
    group
def forward (e : A) (x y : Fin 3 × A) := ((source e).op ((source e).op ((source e).op ((source e).op x y) x) ((source e).op x y)) ((source e).op ((source e).op ((source e).op x y) y) ((source e).op y x)))
/-- The forward identity itself does not need centrality. -/
theorem forward_eq (e : A) (x y : Fin 3 × A) : forward e x y = (target e).op x y := by
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  fin_cases a <;> fin_cases b <;> simp [forward]
def backward (e : A) (x y : Fin 3 × A) := ((target e).op ((target e).op ((target e).op ((target e).op x ((target e).op x x)) ((target e).op x x)) ((target e).op ((target e).op ((target e).op y x) y) y)) ((target e).op ((target e).op y ((target e).op y y)) ((target e).op ((target e).op ((target e).op y x) x) x)))
theorem backward_eq (e : A) (he : ∀ a : A, e * a = a * e) (x y : Fin 3 × A) : backward e x y = (source e).op x y := by
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  fin_cases a <;> fin_cases b <;> simp [backward] <;> group
  all_goals
    have hu : Commute e (u ^ (-1 : ℤ)) := he _
    have hv : Commute e (v ^ (-1 : ℤ)) := he _
    simp only [mul_assoc, (hv.zpow_left (-1)).eq, (hu.zpow_left (-3)).eq]
    group

open FirstOrder.Language
private abbrev tm (a b : (MagmaLanguage.withConstants (∅ : Set (Fin 3 × A))).Term (Fin 2)) :
    (MagmaLanguage.withConstants (∅ : Set (Fin 3 × A))).Term (Fin 2) :=
  Functions.apply₂ (Sum.inl ()) a b
/-- Mutual term recovery, for finite or infinite groups, with a central element. -/
theorem termStructural3545 (e : A) (he : ∀ a : A, e * a = a * e) :
    Law3545.TermStructuralOnMagma (source e) := by
  refine ⟨target e, ?_, ?_, ?_⟩
  · rw [@Law3545.models_iff]
    exact target_law e he
  · refine ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (tm (Term.var 0) (Term.var 1))) (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (tm (Term.var 1) (Term.var 0)))), ?_⟩
    funext v
    change (target e).op (v 0) (v 1) = forward e (v 0) (v 1)
    exact (forward_eq e _ _).symm
  · refine ⟨(tm (tm (tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 0) (Term.var 0))) (tm (tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)) (Term.var 1))) (tm (tm (Term.var 1) (tm (Term.var 1) (Term.var 1))) (tm (tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)) (Term.var 0)))), ?_⟩
    funext v
    change (source e).op (v 0) (v 1) = backward e (v 0) (v 1)
    exact (backward_eq e he _ _).symm

/-- Mutual term recovery, for finite or infinite groups, with a central element. -/
theorem termStructural3342 (e : A) (he : ∀ a : A, e * a = a * e) :
    Law3342.TermStructuralOnMagma (target e) := by
  refine ⟨source e, ?_, ?_, ?_⟩
  · rw [@Law3342.models_iff]
    exact source_law e he
  · refine ⟨(tm (tm (tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 0) (Term.var 0))) (tm (tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)) (Term.var 1))) (tm (tm (Term.var 1) (tm (Term.var 1) (Term.var 1))) (tm (tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)) (Term.var 0)))), ?_⟩
    funext v
    change (source e).op (v 0) (v 1) = backward e (v 0) (v 1)
    exact (backward_eq e he _ _).symm
  · refine ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (tm (Term.var 0) (Term.var 1))) (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (tm (Term.var 1) (Term.var 0)))), ?_⟩
    funext v
    change (target e).op (v 0) (v 1) = forward e (v 0) (v 1)
    exact (forward_eq e _ _).symm

/-- Both twists are right multiplication by the chosen central element. -/
theorem source_twist (e : A) (x : Fin 3 × A) :
    (source e).op x ((source e).op x x) = (x.1, x.2 * e) := by
  obtain ⟨a, u⟩ := x
  fin_cases a <;> simp

theorem target_twist (e : A) (x : Fin 3 × A) :
    (target e).op ((target e).op x x) x = (x.1, x.2 * e) := by
  obtain ⟨a, u⟩ := x
  fin_cases a <;> simp

/-- info: 'NonabelianFiber.source_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_law
/-- info: 'NonabelianFiber.target_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_law
/-- info: 'NonabelianFiber.termStructural3545' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms termStructural3545
/-- info: 'NonabelianFiber.termStructural3342' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms termStructural3342
end NonabelianFiber
