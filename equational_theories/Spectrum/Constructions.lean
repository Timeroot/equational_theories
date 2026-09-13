import equational_theories.Spectrum.Basic
import equational_theories.Equations.All
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases

/-!
Infinite families for laws whose spectra are not full: square orders for central
groupoids, and the odd-order construction of §3.8 of the spectrum note.
-/

open Law Law.MagmaLaw

namespace Spectrum

/-- The natural central groupoid on ordered pairs. -/
@[implicit_reducible]
def central (A : Type*) : Magma (A × A) := ⟨fun x y => (x.2, y.1)⟩

theorem square_168 (k : ℕ) : Law168.HasModel (k ^ 2) :=
  hasModel_of_card (central (Fin k))
    ((@Law168.models_iff _ (central (Fin k))).mpr (fun _ _ _ => rfl))
    (by simp [pow_two])

theorem square_167 (k : ℕ) : Law167.HasModel (k ^ 2) :=
  hasModel_of_card (central (Fin k))
    ((@Law167.models_iff _ (central (Fin k))).mpr (fun _ _ => rfl))
    (by simp [pow_two])

theorem square_1480 (k : ℕ) : Law1480.HasModel (k ^ 2) :=
  hasModel_of_card (central (Fin k))
    ((@Law1480.models_iff _ (central (Fin k))).mpr (fun _ _ _ => rfl))
    (by simp [pow_two])

theorem square_1483 (k : ℕ) : Law1483.HasModel (k ^ 2) :=
  hasModel_of_card (central (Fin k))
    ((@Law1483.models_iff _ (central (Fin k))).mpr (fun _ _ _ => rfl))
    (by simp [pow_two])

theorem square_1485 (k : ℕ) : Law1485.HasModel (k ^ 2) :=
  hasModel_of_card (central (Fin k))
    ((@Law1485.models_iff _ (central (Fin k))).mpr (fun _ _ _ => rfl))
    (by simp [pow_two])

theorem square_1486 (k : ℕ) : Law1486.HasModel (k ^ 2) :=
  hasModel_of_card (central (Fin k))
    ((@Law1486.models_iff _ (central (Fin k))).mpr (fun _ _ _ => rfl))
    (by simp [pow_two])

/-- Adjoin zero to a set carrying a fixed-point-free involution. -/
@[implicit_reducible]
def oddMagma {A : Type*} [DecidableEq A] (σ : A → A) : Magma (Option A) where
  op
    | none, none => none
    | none, some y => some (σ y)
    | some x, none => some x
    | some x, some y => if x = y then none else some y

theorem oddMagma_474 {A : Type*} [DecidableEq A] (σ : A → A)
    (hσ : Function.Involutive σ) (hne : ∀ x, σ x ≠ x) :
    @Equation474 (Option A) (oddMagma σ) := by
  have hs (a : A) : σ (σ a) = a := hσ a
  have hn (a : A) : a ≠ σ a := Ne.symm (hne a)
  rintro (_ | x) (_ | y)
  · rfl
  · simp [Magma.op, hs, hn]
  · simp [Magma.op, hs, hn]
  · by_cases hxy : x = y
    · subst y; simp [Magma.op]
    · simp [Magma.op, hxy, Ne.symm hxy]

theorem oddMagma_1685 {A : Type*} [DecidableEq A] (σ : A → A)
    (hσ : Function.Involutive σ) (hne : ∀ x, σ x ≠ x) :
    @Equation1685 (Option A) (oddMagma σ) := by
  have hs (a : A) : σ (σ a) = a := hσ a
  rintro (_ | x) (_ | y)
  · rfl
  · simp [Magma.op, hne]
  · simp [Magma.op, hne]
  · by_cases hxy : x = y
    · subst y; simp [Magma.op, hs]
    · simp [Magma.op, hxy, Ne.symm hxy]

def flipPair {A : Type*} (x : A × Bool) : A × Bool := (x.1, !x.2)

theorem flipPair_involutive {A : Type*} : Function.Involutive (@flipPair A) := by
  intro x
  simp [flipPair]

theorem flipPair_ne {A : Type*} (x : A × Bool) : flipPair x ≠ x := by
  rcases x with ⟨x, b⟩
  cases b <;> simp [flipPair]

theorem odd_474 (k : ℕ) : Law474.HasModel (2 * k + 1) :=
  hasModel_of_card (oddMagma (@flipPair (Fin k)))
    ((@Law474.models_iff _ (oddMagma (@flipPair (Fin k)))).mpr
      (oddMagma_474 _ flipPair_involutive flipPair_ne))
    (by simp [Nat.mul_comm])

theorem odd_1685 (k : ℕ) : Law1685.HasModel (2 * k + 1) :=
  hasModel_of_card (oddMagma (@flipPair (Fin k)))
    ((@Law1685.models_iff _ (oddMagma (@flipPair (Fin k)))).mpr
      (oddMagma_1685 _ flipPair_involutive flipPair_ne))
    (by simp [Nat.mul_comm])

/-- The four-element core in table (15) of the spectrum note. -/
def core1685 : Fin 4 → Fin 4 → Fin 4
  | 0, y => y
  | 1, 0 => 3
  | 1, 1 => 2
  | 1, 2 => 1
  | 1, 3 => 0
  | 2, 0 => 1
  | 2, 1 => 0
  | 2, 2 => 3
  | 2, 3 => 2
  | 3, 0 => 2
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 1

/-- Extend the four-element core by pairs exchanged by `σ`. -/
@[implicit_reducible]
def evenMagma1685 {A : Type*} [DecidableEq A] (σ : A → A) : Magma (Fin 4 ⊕ A) where
  op
    | .inl x, .inl y => .inl (core1685 x y)
    | .inl x, .inr y => .inr (if x = 0 then σ y else y)
    | .inr x, .inl y => if y = 0 then .inr x else .inl (core1685 (core1685 y 0) 0)
    | .inr x, .inr y => if x = y then .inl 0 else .inr y

theorem evenMagma1685_law {A : Type*} [DecidableEq A] (σ : A → A)
    (hσ : Function.Involutive σ) (hne : ∀ x, σ x ≠ x) :
    @Equation1685 (Fin 4 ⊕ A) (evenMagma1685 σ) := by
  have hs (a : A) : σ (σ a) = a := hσ a
  rintro (x | x) (y | y)
  · fin_cases x <;> fin_cases y <;> rfl
  · fin_cases x <;> simp [Magma.op, core1685, hne]
  · fin_cases y <;> simp [Magma.op, core1685, hne]
  · by_cases hxy : x = y
    · subst y; simp [Magma.op, hs]
    · simp [Magma.op, hxy, Ne.symm hxy]

theorem even_1685 (k : ℕ) : Law1685.HasModel (2 * k + 4) :=
  hasModel_of_card (evenMagma1685 (@flipPair (Fin k)))
    ((@Law1685.models_iff _ (evenMagma1685 (@flipPair (Fin k)))).mpr
      (evenMagma1685_law _ flipPair_involutive flipPair_ne))
    (by simp [Nat.mul_comm, Nat.add_comm])

/-- Table (14) of the note. -/
def core474 : Fin 6 → Fin 6 → Fin 6
  | 0, 0 => 0 | 0, 1 => 2 | 0, 2 => 3 | 0, 3 => 4 | 0, 4 => 5 | 0, 5 => 1
  | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 5 | 1, 3 => 4 | 1, 4 => 3 | 1, 5 => 2
  | 2, 0 => 2 | 2, 1 => 3 | 2, 2 => 0 | 2, 3 => 1 | 2, 4 => 5 | 2, 5 => 4
  | 3, 0 => 3 | 3, 1 => 5 | 3, 2 => 4 | 3, 3 => 0 | 3, 4 => 2 | 3, 5 => 1
  | 4, 0 => 4 | 4, 1 => 2 | 4, 2 => 1 | 4, 3 => 5 | 4, 4 => 0 | 4, 5 => 3
  | 5, 0 => 5 | 5, 1 => 4 | 5, 2 => 3 | 5, 3 => 2 | 5, 4 => 1 | 5, 5 => 0

@[implicit_reducible]
def evenMagma474 {A : Type*} [DecidableEq A] (σ : A → A) : Magma (Fin 6 ⊕ A) where
  op
    | .inl x, .inl y => .inl (core474 x y)
    | .inl x, .inr y => .inr (if x = 0 then σ y else y)
    | .inr x, .inl y => if y = 0 then .inr x else .inl y
    | .inr x, .inr y => if x = y then .inl 0 else .inr y

theorem evenMagma474_law {A : Type*} [DecidableEq A] (σ : A → A)
    (hσ : Function.Involutive σ) (hne : ∀ x, σ x ≠ x) :
    @Equation474 (Fin 6 ⊕ A) (evenMagma474 σ) := by
  have hs (a : A) : σ (σ a) = a := hσ a
  have hn (a : A) : a ≠ σ a := Ne.symm (hne a)
  rintro (x | x) (y | y)
  · fin_cases x <;> fin_cases y <;> rfl
  · fin_cases x <;> simp [Magma.op, core474, hs, hn]
  · fin_cases y <;> simp [Magma.op, core474, hs, hn]
  · by_cases hxy : x = y
    · subst y; simp [Magma.op]
    · simp [Magma.op, hxy, Ne.symm hxy]

theorem even_474 (k : ℕ) : Law474.HasModel (2 * k + 6) :=
  hasModel_of_card (evenMagma474 (@flipPair (Fin k)))
    ((@Law474.models_iff _ (evenMagma474 (@flipPair (Fin k)))).mpr
      (evenMagma474_law _ flipPair_involutive flipPair_ne))
    (by simp [Nat.mul_comm, Nat.add_comm])

theorem hasModel_474_of_not_two_four (n : ℕ) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    Law474.HasModel n := by
  by_cases h0 : n = 0
  · subst n; exact hasModel_zero _
  by_cases hodd : n % 2 = 1
  · convert odd_474 (n / 2) using 1; omega
  · convert even_474 ((n - 6) / 2) using 1; omega

end Spectrum
