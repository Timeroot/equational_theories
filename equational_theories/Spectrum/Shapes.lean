import equational_theories.Spectrum.Basic
import Mathlib.Data.Finset.Basic

/-! Explicit subsets of the **positive** natural numbers occurring in the note.
The existential variables in the square formulas range over naturals: replacing
integer summands by their absolute values gives the same sets. -/

namespace Spectrum

def positiveExcept (excluded : Finset ℕ) : Set ℕ :=
  {n | 0 < n ∧ n ∉ excluded}

def residues (modulus : ℕ) (allowed excluded : Finset ℕ) : Set ℕ :=
  {n | 0 < n ∧ n % modulus ∈ allowed ∧ n ∉ excluded}

def squares : Set ℕ := {n | 0 < n ∧ ∃ k : ℕ, n = k ^ 2}

def twiceSquares : Set ℕ := {n | 0 < n ∧ ∃ k : ℕ, n = 2 * k ^ 2}

def sumTwoSquares : Set ℕ := {n | 0 < n ∧ ∃ k l : ℕ, n = k ^ 2 + l ^ 2}

def oddSumTwoSquares : Set ℕ :=
  {n | ∃ k l : ℕ, n = (2 * k) ^ 2 + (2 * l + 1) ^ 2}

def shiftedSquares : Set ℕ := {n | ∃ k : ℕ, 3 ≤ k ∧ n = k ^ 2 + 2}

def powersTwo : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

/-- All sufficiently large natural numbers belong to the (positive) spectrum. -/
def CofiniteSpectrum (L : Law.NatMagmaLaw) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n ∈ L.spectrum

end Spectrum
