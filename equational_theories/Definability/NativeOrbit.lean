import DefOrbit
import equational_theories.Definability.CachedWordImages
import Mathlib.Algebra.BigOperators.Fin

/-! Connect a compiled interval check to the finite orbit certificates. -/
namespace DefOrbit

theorem allBelow_spec (f : Nat → Bool) (n : Nat) :
    allBelow f n = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow]
    split <;> rename_i h
    · rw [ih]
      constructor
      · intro ha i hi
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
        · exact ha i hi
        · exact h
      · intro ha i hi
        exact ha i (Nat.lt_succ_of_lt hi)
    · simp only [Bool.false_eq_true, false_iff]
      intro ha
      exact h (ha n (Nat.lt_succ_self n))

end DefOrbit

/-- info: 'DefOrbit.allBelow_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DefOrbit.allBelow_spec
