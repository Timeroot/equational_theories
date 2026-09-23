import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status
import equational_theories.Equations.All
import Mathlib.Tactic

/-! # Semisymmetric twisting data for E1719 -/

namespace Spectrum

structure SemisymmetricTwist (Q : Type*) where
  op : Q → Q → Q
  turn : Q → Q
  semi : ∀ x y, op y (op x y) = x
  turn_three : ∀ x, turn (turn (turn x)) = x
  diagonal : ∀ x, op (turn (turn x)) x = turn x

namespace SemisymmetricTwist
variable {Q : Type*}

@[implicit_reducible] def magma (T : SemisymmetricTwist Q) : Magma Q :=
  ⟨fun x y => T.op (T.turn (T.turn x)) y⟩

theorem equation1719 (T : SemisymmetricTwist Q) : @Equation1719 Q T.magma := by
  intro x y
  change x = T.op (T.turn (T.turn (T.op (T.turn (T.turn y)) y)))
    (T.op (T.turn (T.turn (T.op (T.turn (T.turn x)) x))) y)
  rw [T.diagonal, T.diagonal, T.turn_three, T.turn_three, T.semi]

/-- The squaring map of every E1719 magma has cube equal to the identity. -/
theorem square_three [Magma Q] (h : Equation1719 Q) (x : Q) :
    ((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)) = x :=
  (h x (x ◇ x)).symm

/-- Recover the semisymmetric operation and its twisting permutation. -/
def ofEquation1719 [Magma Q] (h : Equation1719 Q) : SemisymmetricTwist Q where
  op x y := (x ◇ x) ◇ y
  turn x := x ◇ x
  semi x y := (h x y).symm
  turn_three := square_three h
  diagonal x := by rw [square_three h]

/-- A chosen oriented triangle absorbs the only possibly non-idempotent point. -/
noncomputable def ofTriangle (op : Q → Q → Q) (b c d : Q)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : ∀ x y, op y (op x y) = x)
    (hi : ∀ x, x ≠ b → op x x = x)
    (hdb : op d b = c) (hbc' : op b c = d) (hcd' : op c d = b) :
    SemisymmetricTwist Q := by
  classical
  let s := fun x => if x = b then c else if x = c then d else if x = d then b else x
  refine ⟨op, s, hs, ?_, ?_⟩
  · intro x
    by_cases hb : x = b
    · subst x; simp [s, hbc.symm, hbd.symm, hcd.symm]
    by_cases hc : x = c
    · subst x; simp [s, hbc.symm, hbd.symm, hcd.symm]
    by_cases hd : x = d
    · subst x; simp [s, hbc.symm, hbd.symm, hcd.symm]
    simp [s, hb, hc, hd]
  · intro x
    by_cases hb : x = b
    · subst x; simpa [s, hbc.symm, hbd.symm, hcd.symm] using hdb
    by_cases hc : x = c
    · subst x; simpa [s, hbc.symm, hbd.symm, hcd.symm] using hbc'
    by_cases hd : x = d
    · subst x; simpa [s, hbc.symm, hbd.symm, hcd.symm] using hcd'
    simpa [s, hb, hc, hd] using hi x hb

end SemisymmetricTwist
end Spectrum
