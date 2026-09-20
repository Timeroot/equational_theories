import equational_theories.Equations.All
import Mathlib.Data.Fin.VecNotation

/-!
# Rejected square-iteration candidates for the residual definability rows

These certificates concern only operations of the form
`q^[a] (M.op (q^[b] x) (q^[c] y))`, where `q x = M.op x x`.
They do not assert any negative definability cell.

Run with `lake env lean scripts/check_definability_square_candidates.lean`.
All finite calculations use kernel `decide`.
-/

namespace ResidualSquareCandidates

variable {G : Type}

def iter (q : G → G) : Nat → G → G
  | 0 => id
  | n + 1 => fun x => q (iter q n x)

def phase {k : Nat} (zero : Fin k) (step : Fin k → Fin k) : Nat → Fin k
  | 0 => zero
  | n + 1 => step (phase zero step n)

theorem iter_eq_phase {k : Nat} (zero : Fin k) (step : Fin k → Fin k)
    (q : G → G) (powers : Fin k → G → G)
    (h0 : ∀ x, powers zero x = x)
    (hs : ∀ i x, q (powers i x) = powers (step i) x) (n : Nat) (x : G) :
    iter q n x = powers (phase zero step n) x := by
  induction n with
  | zero => exact (h0 x).symm
  | succ n ih => simpa only [iter, phase, ih] using hs (phase zero step n) x

@[implicit_reducible] def derived (M : Magma G) (a b c : Nat) : Magma G where
  op x y := iter (fun z => M.op z z) a
    (M.op (iter (fun z => M.op z z) b x) (iter (fun z => M.op z z) c y))

namespace E3342

@[implicit_reducible] def source : Magma (Fin 8) where
  op := ![![4, 5, 2, 4, 3, 5, 5, 0],
    ![5, 5, 1, 5, 4, 6, 5, 7],
    ![5, 6, 0, 2, 1, 0, 1, 0],
    ![4, 5, 5, 4, 0, 2, 5, 3],
    ![0, 7, 0, 3, 1, 1, 4, 1],
    ![2, 1, 0, 5, 0, 0, 6, 1],
    ![5, 5, 6, 5, 7, 1, 5, 4],
    ![3, 4, 1, 0, 1, 0, 7, 1]]

theorem source_law : @Equation3342 (Fin 8) source := by decide

def square (x : Fin 8) : Fin 8 := source.op x x

def step : Fin 5 → Fin 5 := ![1, 2, 3, 4, 1]

def powers (i : Fin 5) (x : Fin 8) : Fin 8 := iter square i.val x

theorem powers_step : ∀ i x, square (powers i x) = powers (step i) x := by decide

theorem powers_zero (x : Fin 8) : powers 0 x = x := rfl

@[implicit_reducible] def candidate (a b c : Fin 5) : Magma (Fin 8) where
  op x y := powers a (source.op (powers b x) (powers c y))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finite_failure : ∀ a b c, ¬ @Equation4405 (Fin 8) (candidate a b c) := by decide

theorem square_family_failure (a b c : Nat) :
    ¬ @Equation4405 (Fin 8) (derived source a b c) := by
  have hi := iter_eq_phase (0 : Fin 5) step square powers powers_zero powers_step
  have he : derived source a b c =
      candidate (phase 0 step a) (phase 0 step b) (phase 0 step c) := by
    apply congrArg Magma.mk
    funext x y
    change iter square a (source.op (iter square b x) (iter square c y)) = _
    simp only [hi]
  rw [he]
  exact finite_failure _ _ _

/-- info: 'ResidualSquareCandidates.E3342.square_family_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms square_family_failure

end E3342

namespace E3545

@[implicit_reducible] def source : Magma (Fin 8) where
  op := ![![2, 6, 0, 3, 2, 4, 6, 6],
    ![6, 6, 5, 7, 6, 2, 1, 6],
    ![4, 2, 1, 0, 0, 1, 6, 5],
    ![6, 1, 6, 4, 3, 0, 4, 7],
    ![2, 6, 4, 6, 2, 0, 3, 6],
    ![0, 5, 1, 6, 4, 1, 0, 2],
    ![3, 7, 0, 4, 6, 6, 4, 1],
    ![6, 6, 2, 1, 6, 5, 7, 6]]

theorem source_law : @Equation3545 (Fin 8) source := by decide

def square (x : Fin 8) : Fin 8 := source.op x x

def step : Fin 5 → Fin 5 := ![1, 2, 3, 4, 1]

def powers (i : Fin 5) (x : Fin 8) : Fin 8 := iter square i.val x

theorem powers_step : ∀ i x, square (powers i x) = powers (step i) x := by decide

theorem powers_zero (x : Fin 8) : powers 0 x = x := rfl

@[implicit_reducible] def candidate (a b c : Fin 5) : Magma (Fin 8) where
  op x y := powers a (source.op (powers b x) (powers c y))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finite_failure : ∀ a b c, ¬ @Equation4405 (Fin 8) (candidate a b c) := by decide

theorem square_family_failure (a b c : Nat) :
    ¬ @Equation4405 (Fin 8) (derived source a b c) := by
  have hi := iter_eq_phase (0 : Fin 5) step square powers powers_zero powers_step
  have he : derived source a b c =
      candidate (phase 0 step a) (phase 0 step b) (phase 0 step c) := by
    apply congrArg Magma.mk
    funext x y
    change iter square a (source.op (iter square b x) (iter square c y)) = _
    simp only [hi]
  rw [he]
  exact finite_failure _ _ _

/-- info: 'ResidualSquareCandidates.E3545.square_family_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms square_family_failure

end E3545

namespace E3352

@[implicit_reducible] def source : Magma (Fin 7) where
  op := ![![4, 4, 0, 0, 1, 0, 5],
    ![0, 6, 2, 5, 4, 6, 5],
    ![1, 0, 0, 2, 2, 2, 5],
    ![4, 5, 0, 5, 2, 5, 5],
    ![4, 2, 1, 4, 2, 4, 5],
    ![4, 6, 0, 5, 2, 3, 1],
    ![1, 5, 1, 5, 1, 1, 1]]

theorem source_law : @Equation3352 (Fin 7) source := by decide

def square (x : Fin 7) : Fin 7 := source.op x x

def step : Fin 6 → Fin 6 := ![1, 2, 3, 4, 5, 0]

def powers (i : Fin 6) (x : Fin 7) : Fin 7 := iter square i.val x

theorem powers_step : ∀ i x, square (powers i x) = powers (step i) x := by decide

theorem powers_zero (x : Fin 7) : powers 0 x = x := rfl

@[implicit_reducible] def candidate (a b c : Fin 6) : Magma (Fin 7) where
  op x y := powers a (source.op (powers b x) (powers c y))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem finite_failure : ∀ a b c, ¬ @Equation4408 (Fin 7) (candidate a b c) := by decide

theorem square_family_failure (a b c : Nat) :
    ¬ @Equation4408 (Fin 7) (derived source a b c) := by
  have hi := iter_eq_phase (0 : Fin 6) step square powers powers_zero powers_step
  have he : derived source a b c =
      candidate (phase 0 step a) (phase 0 step b) (phase 0 step c) := by
    apply congrArg Magma.mk
    funext x y
    change iter square a (source.op (iter square b x) (iter square c y)) = _
    simp only [hi]
  rw [he]
  exact finite_failure _ _ _

/-- info: 'ResidualSquareCandidates.E3352.square_family_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms square_family_failure

end E3352

end ResidualSquareCandidates
