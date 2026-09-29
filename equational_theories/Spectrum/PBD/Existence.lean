import equational_theories.Spectrum.PBD.Model
import Mathlib.Algebra.GCDMonoid.Finset

/-! A finite pairwise balanced design and the precise Wilson existence input.
This module defines the input and proves its consequences; it does not assume
Wilson's theorem as an axiom. The required instances are proved in `WilsonInstances`. -/
namespace Spectrum.PBD

structure PairwiseBalanced (K : Finset ℕ) (n : ℕ) where
  blocks : Finset (Finset (Fin n))
  sizes : ∀ b ∈ blocks, b.card ∈ K
  cover : ∀ x y : Fin n, x ≠ y → ∃! b : blocks, x ∈ b.val ∧ y ∈ b.val

def HasPBD (K : Finset ℕ) (n : ℕ) : Prop := Nonempty (PairwiseBalanced K n)

theorem HasPBD.model {K : Finset ℕ} {n : ℕ} {L : BinaryLaw} (h : HasPBD K n)
    (seeds : ∀ k ∈ K, Nonempty (Model L (Fin k))) : Nonempty (Model L (Fin n)) := by
  classical
  obtain ⟨D⟩ := h
  let B (b : D.blocks) : Set (Fin n) := b.val
  have models (b : D.blocks) : Nonempty (Model L (B b)) := by
    obtain ⟨M⟩ := seeds b.val.card (D.sizes b.val b.property)
    exact ⟨M.ofCard (by simp [B])⟩
  exact ⟨Model.glue B (fun b => (models b).some) D.cover⟩

/-- The two necessary divisibility conditions in Wilson's PBD theorem. -/
def Admissible (K : Finset ℕ) (n : ℕ) : Prop :=
  K.gcd (fun k => k-1) ∣ n-1 ∧ K.gcd (fun k => k*(k-1)) ∣ n*(n-1)

/-- The conclusion of Wilson's theorem for one fixed finite block-size set. -/
def WilsonExistence (K : Finset ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Admissible K n → HasPBD K n

/-- The restricted design tail needed for the residue-filling argument. -/
def ResidueTail (K : Finset ℕ) (p : ℕ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, C ≤ n → (n % p = 0 ∨ n % p = 1) → HasPBD K n

private theorem two_dvd_consecutive (n : ℕ) : 2 ∣ n*(n-1) := by
  by_cases h : n % 2 = 0
  · exact (Nat.dvd_of_mod_eq_zero h).mul_right _
  · exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _

theorem admissible_7_9_16 {n : ℕ} (hn : n % 3 = 0 ∨ n % 3 = 1) :
    Admissible {7,9,16} n := by
  have h3 : 3 ∣ n*(n-1) := by
    rcases hn with h | h
    · exact (Nat.dvd_of_mod_eq_zero h).mul_right _
    · exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _
  have h6 : 6 ∣ n*(n-1) := (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd
    (two_dvd_consecutive n) h3
  change ({7,9,16} : Finset ℕ).gcd (fun k => k-1) ∣ n-1 ∧
    ({7,9,16} : Finset ℕ).gcd (fun k => k*(k-1)) ∣ n*(n-1)
  rw [show ({7,9,16} : Finset ℕ).gcd (fun k => k-1) = 1 from by decide,
    show ({7,9,16} : Finset ℕ).gcd (fun k => k*(k-1)) = 6 from by decide]
  exact ⟨one_dvd _, h6⟩

theorem admissible_5_11_16 {n : ℕ} (hn : n % 5 = 0 ∨ n % 5 = 1) :
    Admissible {5,11,16} n := by
  have h5 : 5 ∣ n*(n-1) := by
    rcases hn with h | h
    · exact (Nat.dvd_of_mod_eq_zero h).mul_right _
    · exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _
  have h10 : 10 ∣ n*(n-1) := (show Nat.Coprime 2 5 by decide).mul_dvd_of_dvd_of_dvd
    (two_dvd_consecutive n) h5
  change ({5,11,16} : Finset ℕ).gcd (fun k => k-1) ∣ n-1 ∧
    ({5,11,16} : Finset ℕ).gcd (fun k => k*(k-1)) ∣ n*(n-1)
  rw [show ({5,11,16} : Finset ℕ).gcd (fun k => k-1) = 1 from by decide,
    show ({5,11,16} : Finset ℕ).gcd (fun k => k*(k-1)) = 10 from by decide]
  exact ⟨one_dvd _, h10⟩

theorem WilsonExistence.tail_7_9_16 (h : WilsonExistence {7,9,16}) :
    ResidueTail {7,9,16} 3 := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C, fun n hn hr => hC n hn (admissible_7_9_16 hr)⟩

theorem WilsonExistence.tail_5_11_16 (h : WilsonExistence {5,11,16}) :
    ResidueTail {5,11,16} 5 := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C, fun n hn hr => hC n hn (admissible_5_11_16 hr)⟩

end Spectrum.PBD
