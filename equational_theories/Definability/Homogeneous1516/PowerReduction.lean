import equational_theories.Definability.GLTwo1516
import Mathlib.Algebra.Field.ZMod

/-! Power conjugation reduces the nonzero diagonal multipliers of a homogeneous
E1516 operation over F₂₉ to five representatives. All finite arithmetic here is
checked by Lean's kernel; the exclusions of the representatives are separate. -/

namespace Definability.Homogeneous1516

open Definability.GLTwo1516

section Transport
variable {K : Type} [Field K]

/-- Transport an operation along a power permutation, with inverse exponent `l`. -/
def powerConjugate (p : K → K → K) (k l : ℕ) (x y : K) : K :=
  (p (x ^ l) (y ^ l)) ^ k

lemma powerConjugate_homogeneous (p : K → K → K) (k l : ℕ)
    (hinv : ∀ x : K, (x ^ l) ^ k = x) (hp : Homogeneous p) :
    Homogeneous (powerConjugate p k l) := by
  intro t x y ht
  simp only [powerConjugate, mul_pow]
  rw [hp (t ^ l) (x ^ l) (y ^ l) (pow_ne_zero _ ht), mul_pow, hinv]

lemma powerConjugate_law (p : K → K → K) (k l : ℕ)
    (hkl : ∀ x : K, (x ^ k) ^ l = x) (hlk : ∀ x : K, (x ^ l) ^ k = x)
    (hp : ∀ x y, x = p (p y y) (p x (p x y))) :
    ∀ x y, x = powerConjugate p k l (powerConjugate p k l y y)
      (powerConjugate p k l x (powerConjugate p k l x y)) := by
  intro x y
  simp only [powerConjugate, hkl]
  exact (hlk x).symm.trans (congrArg (fun z => z ^ k) (hp (x ^ l) (y ^ l)))

lemma powerConjugate_diagonal (p : K → K → K) (k l : ℕ) :
    powerConjugate p k l 1 1 = (p 1 1) ^ k := by
  simp [powerConjugate]

end Transport

local instance : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- One exponent for each automorphism of the multiplicative group F₂₉×. -/
def exponent : Fin 12 → ℕ := ![1, 3, 5, 9, 11, 13, 15, 17, 19, 23, 25, 27]

/-- The inverse exponents modulo 28, in the same order. -/
def inverseExponent : Fin 12 → ℕ := ![1, 19, 17, 25, 23, 13, 15, 5, 3, 11, 9, 27]

lemma power_inverse : ∀ (i : Fin 12) (x : ZMod 29),
    (x ^ exponent i) ^ inverseExponent i = x ∧
    (x ^ inverseExponent i) ^ exponent i = x := by
  decide +kernel

/-- Representatives for the nonidentity multiplicative orders 28, 14, 7, 4, 2. -/
def Representative (s : ZMod 29) : Prop :=
  s = 2 ∨ s = 4 ∨ s = 7 ∨ s = 12 ∨ s = 28

instance (s : ZMod 29) : Decidable (Representative s) := inferInstanceAs
  (Decidable (s = 2 ∨ s = 4 ∨ s = 7 ∨ s = 12 ∨ s = 28))

lemma power_representative : ∀ s : ZMod 29, s ≠ 0 → s ≠ 1 →
    ∃ i : Fin 12, Representative (s ^ exponent i) := by
  decide +kernel

/-- Excluding five diagonal multipliers excludes every nonzero multiplier other
than 1, since power conjugation preserves homogeneity and the E1516 law. -/
theorem diagonal_one_of_representatives_excluded
    (hex : ∀ p : ZMod 29 → ZMod 29 → ZMod 29, Homogeneous p →
      (∀ x y, x = p (p y y) (p x (p x y))) → ¬ Representative (p 1 1))
    (p : ZMod 29 → ZMod 29 → ZMod 29) (hh : Homogeneous p)
    (hlaw : ∀ x y, x = p (p y y) (p x (p x y))) (hn : p 1 1 ≠ 0) :
    p 1 1 = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ := power_representative (p 1 1) hn hne
  let q := powerConjugate p (exponent i) (inverseExponent i)
  have hq : Homogeneous q := powerConjugate_homogeneous p _ _
    (fun x => (power_inverse i x).2) hh
  have hqlaw : ∀ x y, x = q (q y y) (q x (q x y)) := powerConjugate_law p _ _
    (fun x => (power_inverse i x).1) (fun x => (power_inverse i x).2) hlaw
  apply hex q hq hqlaw
  simpa only [q, powerConjugate_diagonal] using hi

/-- info: 'Definability.Homogeneous1516.diagonal_one_of_representatives_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms diagonal_one_of_representatives_excluded

end Definability.Homogeneous1516
