import equational_theories.Definability.Basic
import equational_theories.Equations.All
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

/-!
Explicit mutual term definitions on a family of E3342 models with carrier
`Fin 3 × A`, for any additive commutative group A and any distinguished e.
This is a family result; it does not prove E3342 → E4405 or E3342 → E3545 on the definability board.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace FiberRecovery

variable {A : Type} [AddCommGroup A]

def base : Fin 3 → Fin 3 → Fin 3 := ![![1, 0, 2], ![0, 2, 1], ![2, 1, 0]]
def delta : Fin 3 → Fin 3 → Fin 3 := ![![0, 1, 2], ![2, 0, 1], ![1, 2, 0]]

@[implicit_reducible] def source (e : A) : Magma (Fin 3 × A) where
  op x y := (base x.1 y.1,
    if delta x.1 y.1 = 0 then 0 else if delta x.1 y.1 = 1 then x.2 - y.2 + e
    else -x.2 + y.2)

@[implicit_reducible] def target (e : A) : Magma (Fin 3 × A) where
  op x y := (base x.1 y.1,
    if delta x.1 y.1 = 0 then 0 else if delta x.1 y.1 = 1 then -x.2 - y.2 + e
    else -y.2 + e)

@[simp] theorem source_00 (e u v : A) : (source e).op (0, u) (0, v) = (1, 0) := rfl
@[simp] theorem source_01 (e u v : A) : (source e).op (0, u) (1, v) = (0, u - v + e) := rfl
@[simp] theorem source_02 (e u v : A) : (source e).op (0, u) (2, v) = (2, -u + v) := rfl
@[simp] theorem source_10 (e u v : A) : (source e).op (1, u) (0, v) = (0, -u + v) := rfl
@[simp] theorem source_11 (e u v : A) : (source e).op (1, u) (1, v) = (2, 0) := rfl
@[simp] theorem source_12 (e u v : A) : (source e).op (1, u) (2, v) = (1, u - v + e) := rfl
@[simp] theorem source_20 (e u v : A) : (source e).op (2, u) (0, v) = (2, u - v + e) := rfl
@[simp] theorem source_21 (e u v : A) : (source e).op (2, u) (1, v) = (1, -u + v) := rfl
@[simp] theorem source_22 (e u v : A) : (source e).op (2, u) (2, v) = (0, 0) := rfl
@[simp] theorem target_00 (e u v : A) : (target e).op (0, u) (0, v) = (1, 0) := rfl
@[simp] theorem target_01 (e u v : A) : (target e).op (0, u) (1, v) = (0, -u - v + e) := rfl
@[simp] theorem target_02 (e u v : A) : (target e).op (0, u) (2, v) = (2, -v + e) := rfl
@[simp] theorem target_10 (e u v : A) : (target e).op (1, u) (0, v) = (0, -v + e) := rfl
@[simp] theorem target_11 (e u v : A) : (target e).op (1, u) (1, v) = (2, 0) := rfl
@[simp] theorem target_12 (e u v : A) : (target e).op (1, u) (2, v) = (1, -u - v + e) := rfl
@[simp] theorem target_20 (e u v : A) : (target e).op (2, u) (0, v) = (2, -u - v + e) := rfl
@[simp] theorem target_21 (e u v : A) : (target e).op (2, u) (1, v) = (1, -v + e) := rfl
@[simp] theorem target_22 (e u v : A) : (target e).op (2, u) (2, v) = (0, 0) := rfl

theorem source_law (e : A) : @Equation3342 (Fin 3 × A) (source e) := by
  intro x y
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  fin_cases a <;> fin_cases b <;> simp <;> abel

theorem target_law (e : A) : @Equation4405 (Fin 3 × A) (target e) := by
  intro x y
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  fin_cases a <;> fin_cases b <;> simp <;> abel

def forward (e : A) (x y : Fin 3 × A) : Fin 3 × A :=
  ((source e).op ((source e).op ((source e).op ((source e).op ((source e).op x x) y) x) y) ((source e).op ((source e).op ((source e).op ((source e).op x x) ((source e).op x x)) ((source e).op x y)) ((source e).op ((source e).op ((source e).op x x) ((source e).op x x)) ((source e).op ((source e).op x x) ((source e).op y x)))))

def backward (e : A) (x y : Fin 3 × A) : Fin 3 × A :=
  ((target e).op ((target e).op ((target e).op ((target e).op x y) x) ((target e).op ((target e).op x y) y)) ((target e).op ((target e).op ((target e).op y y) y) ((target e).op ((target e).op x y) ((target e).op y y))))

theorem forward_eq (e : A) (x y : Fin 3 × A) : forward e x y = (target e).op x y := by
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  fin_cases a <;> fin_cases b <;> simp [forward] <;> abel

theorem backward_eq (e : A) (x y : Fin 3 × A) : backward e x y = (source e).op x y := by
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  fin_cases a <;> fin_cases b <;> simp [backward] <;> abel

open FirstOrder.Language

private abbrev tm (a b : (MagmaLanguage.withConstants (∅ : Set (Fin 3 × A))).Term (Fin 2)) :
    (MagmaLanguage.withConstants (∅ : Set (Fin 3 × A))).Term (Fin 2) :=
  Functions.apply₂ (Sum.inl ()) a b

/-- Uniform terms give mutual recovery on this family, including infinite groups. -/
theorem termStructural (e : A) : Law4405.TermStructuralOnMagma (source e) := by
  refine ⟨target e, ?_, ?_, ?_⟩
  · rw [@Law4405.models_iff]
    exact target_law e
  · refine ⟨(tm (tm (tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)) (Term.var 0)) (Term.var 1)) (tm (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 0) (Term.var 1))) (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0)))))), ?_⟩
    funext v
    change (target e).op (v 0) (v 1) = forward e (v 0) (v 1)
    exact (forward_eq e _ _).symm
  · refine ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1))) (tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 1)) (tm (Term.var 1) (Term.var 1))))), ?_⟩
    funext v
    change (source e).op (v 0) (v 1) = backward e (v 0) (v 1)
    exact (backward_eq e _ _).symm

/-- info: 'FiberRecovery.source_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_law

/-- info: 'FiberRecovery.target_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_law

/-- info: 'FiberRecovery.termStructural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms termStructural


/-- The E3545 companion of the same source family. -/
@[implicit_reducible] def middle (e : A) : Magma (Fin 3 × A) where
  op x y := (base x.1 y.1,
    if delta x.1 y.1 = 0 then 0 else if delta x.1 y.1 = 1 then x.2 - y.2 + e + e
    else -x.2 + y.2 + e)

@[simp] theorem middle_00 (e u v : A) : (middle e).op (0, u) (0, v) = (1, 0) := rfl
@[simp] theorem middle_01 (e u v : A) : (middle e).op (0, u) (1, v) = (0, u - v + e + e) := rfl
@[simp] theorem middle_02 (e u v : A) : (middle e).op (0, u) (2, v) = (2, -u + v + e) := rfl
@[simp] theorem middle_10 (e u v : A) : (middle e).op (1, u) (0, v) = (0, -u + v + e) := rfl
@[simp] theorem middle_11 (e u v : A) : (middle e).op (1, u) (1, v) = (2, 0) := rfl
@[simp] theorem middle_12 (e u v : A) : (middle e).op (1, u) (2, v) = (1, u - v + e + e) := rfl
@[simp] theorem middle_20 (e u v : A) : (middle e).op (2, u) (0, v) = (2, u - v + e + e) := rfl
@[simp] theorem middle_21 (e u v : A) : (middle e).op (2, u) (1, v) = (1, -u + v + e) := rfl
@[simp] theorem middle_22 (e u v : A) : (middle e).op (2, u) (2, v) = (0, 0) := rfl

theorem middle_law (e : A) : @Equation3545 (Fin 3 × A) (middle e) := by
  intro x y
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  fin_cases a <;> fin_cases b <;> simp <;> abel

def forward3545 (e : A) (x y : Fin 3 × A) : Fin 3 × A :=
  ((source e).op ((source e).op ((source e).op ((source e).op x y) x) ((source e).op x y)) ((source e).op ((source e).op ((source e).op x y) y) ((source e).op y x)))

theorem forward3545_eq (e : A) (x y : Fin 3 × A) :
    forward3545 e x y = (middle e).op x y := by
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  fin_cases a <;> fin_cases b <;> simp [forward3545] <;> abel

def backward3545 (e : A) (x y : Fin 3 × A) : Fin 3 × A :=
  ((middle e).op ((middle e).op ((middle e).op ((middle e).op ((middle e).op x x) x) ((middle e).op ((middle e).op y y) ((middle e).op y y))) ((middle e).op ((middle e).op ((middle e).op x x) ((middle e).op y y)) y)) ((middle e).op ((middle e).op ((middle e).op ((middle e).op x x) x) y) ((middle e).op ((middle e).op ((middle e).op x x) ((middle e).op x x)) ((middle e).op ((middle e).op x x) ((middle e).op y y)))))

theorem backward3545_eq (e : A) (x y : Fin 3 × A) :
    backward3545 e x y = (source e).op x y := by
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  fin_cases a <;> fin_cases b <;> simp [backward3545] <;> abel

theorem termStructural3545 (e : A) : Law3545.TermStructuralOnMagma (source e) := by
  refine ⟨middle e, ?_, ?_, ?_⟩
  · rw [@Law3545.models_iff]
    exact middle_law e
  · refine ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (tm (Term.var 0) (Term.var 1))) (tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (tm (Term.var 1) (Term.var 0)))), ?_⟩
    funext v
    change (middle e).op (v 0) (v 1) = forward3545 e (v 0) (v 1)
    exact (forward3545_eq e _ _).symm
  · refine ⟨(tm (tm (tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (tm (tm (Term.var 1) (Term.var 1)) (tm (Term.var 1) (Term.var 1)))) (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1))) (Term.var 1))) (tm (tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)) (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 1)))))), ?_⟩
    funext v
    change (source e).op (v 0) (v 1) = backward3545 e (v 0) (v 1)
    exact (backward3545_eq e _ _).symm

/-- info: 'FiberRecovery.termStructural3545' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms termStructural3545

/-- The E3342 twist can have arbitrary additive order. -/
theorem source_twist (e : A) (x : Fin 3 × A) :
    (source e).op x ((source e).op x x) = (x.1, x.2 + e) := by
  obtain ⟨a, u⟩ := x
  fin_cases a <;> simp

/-- The E3545 twist has the same translation behavior. -/
theorem middle_twist (e : A) (x : Fin 3 × A) :
    (middle e).op ((middle e).op x x) x = (x.1, x.2 + e) := by
  obtain ⟨a, u⟩ := x
  fin_cases a <;> simp

/-- info: 'FiberRecovery.source_twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_twist
/-- info: 'FiberRecovery.middle_twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms middle_twist

end FiberRecovery
