import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree

/-!
# Irreducibility of quartics and quintics by a finite check

The last orders the definability board needs have degree four and five, and Mathlib's decidable
criteria stop at degree three: `Monic.irreducible_iff_roots_eq_zero_of_degree_le_three` for the
general case, and Selmer's theorem for `X ^ n - X - 1`. Nothing covers, say,
`X ^ 4 + 2 * X ^ 3 + 3 * X ^ 2 + X + 1`.

But `Monic.irreducible_iff_lt_natDegree_lt` only asks about monic factors of degree at most
`n / 2`, which for `n = 4` and `n = 5` alike is `2`. A monic factor of degree one is `X + C a` and
contributes a root; a monic factor of degree two is `X ^ 2 + C a * X + C b`, and its cofactor is
monic of degree `n - 2`, so both are given by their coefficients. Comparing coefficients turns the
whole question into two first-order statements about the coefficient ring, and over a `ZMod m`
those are `decide`. `Monic.irreducible_of_irreducible_map` then lifts the result to `ℤ[X]`.

The `h2` hypotheses below are exactly the coefficient equations of `(X ^ 2 + a X + b) * (…)`, so a
model contributes its `q` and a prime of good reduction and nothing else.
-/

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- A monic quadratic is determined by its two low coefficients. -/
theorem Monic.eq_X_sq_add {p : R[X]} (hm : p.Monic) (hd : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  have h2 : p.coeff 2 = 1 := by rw [← hd]; exact hm.coeff_natDegree
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp [h2]
  | (k + 3) => simp [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k + 3)]

/-- A monic cubic is determined by its three low coefficients. -/
theorem Monic.eq_X_cube_add {p : R[X]} (hm : p.Monic) (hd : p.natDegree = 3) :
    p = X ^ 3 + C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  have h3 : p.coeff 3 = 1 := by rw [← hd]; exact hm.coeff_natDegree
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp [h3]
  | (k + 4) => simp [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k + 4)]

/-- A product of two monic quadratics, in the coefficient basis. -/
theorem quartic_expand (a b c d : R) :
    (X ^ 2 + C a * X + C b) * (X ^ 2 + C c * X + C d)
      = X ^ 4 + C (a + c) * X ^ 3 + C (b + d + a * c) * X ^ 2 + C (a * d + b * c) * X
        + C (b * d) := by
  simp only [C_add, C_mul]; ring

/-- A monic quadratic times a monic cubic, in the coefficient basis. -/
theorem quintic_expand (a b c d e : R) :
    (X ^ 2 + C a * X + C b) * (X ^ 3 + C c * X ^ 2 + C d * X + C e)
      = X ^ 5 + C (a + c) * X ^ 4 + C (b + d + a * c) * X ^ 3 + C (e + a * d + b * c) * X ^ 2
        + C (a * e + b * d) * X + C (b * e) := by
  simp only [C_add, C_mul]; ring

/-- Two quartics written in the coefficient basis are equal only coefficientwise. -/
theorem quartic_coeff {a b c d a' b' c' d' : R}
    (h : (X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : R[X])
       = X ^ 4 + C a' * X ^ 3 + C b' * X ^ 2 + C c' * X + C d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := congrArg (fun r => Polynomial.coeff r 3) h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at e
    norm_num at e
    exact e
  · have e := congrArg (fun r => Polynomial.coeff r 2) h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at e
    norm_num at e
    exact e
  · have e := congrArg (fun r => Polynomial.coeff r 1) h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at e
    norm_num at e
    exact e
  · have e := congrArg (fun r => Polynomial.coeff r 0) h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at e
    norm_num at e
    exact e

/-- Two quintics written in the coefficient basis are equal only coefficientwise. -/
theorem quintic_coeff {a b c d e a' b' c' d' e' : R}
    (h : (X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e : R[X])
       = X ^ 5 + C a' * X ^ 4 + C b' * X ^ 3 + C c' * X ^ 2 + C d' * X + C e') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have g := congrArg (fun r => Polynomial.coeff r 4) h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at g
    norm_num at g
    exact g
  · have g := congrArg (fun r => Polynomial.coeff r 3) h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at g
    norm_num at g
    exact g
  · have g := congrArg (fun r => Polynomial.coeff r 2) h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at g
    norm_num at g
    exact g
  · have g := congrArg (fun r => Polynomial.coeff r 1) h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at g
    norm_num at g
    exact g
  · have g := congrArg (fun r => Polynomial.coeff r 0) h
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at g
    norm_num at g
    exact g

variable [IsDomain R]

/-- A monic quartic with no root and no factorization into two monic quadratics is irreducible.
Both hypotheses are quantifier statements about the coefficient ring alone. -/
theorem irreducible_quartic {p : R[X]} (c₃ c₂ c₁ c₀ : R)
    (hp : p = X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀)
    (h1 : ∀ x : R, x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ ≠ 0)
    (h2 : ∀ a b c d : R, ¬(a + c = c₃ ∧ b + d + a * c = c₂ ∧ a * d + b * c = c₁ ∧
      b * d = c₀)) :
    Irreducible p := by
  have hm : p.Monic := by rw [hp]; monicity!
  have hdeg : p.natDegree = 4 := by rw [hp]; compute_degree!
  have hne1 : p ≠ 1 := fun h => by simp [h] at hdeg
  rw [hm.irreducible_iff_lt_natDegree_lt hne1]
  rintro g hg hmem ⟨f, hf⟩
  rw [Finset.mem_Ioc, hdeg] at hmem
  have hfm : f.Monic := hg.of_mul_monic_left (hf ▸ hm)
  have hsum : g.natDegree + f.natDegree = 4 := by
    rw [← hdeg, hf, hg.natDegree_mul hfm]
  obtain hgd | hgd : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
  · refine h1 (-(g.coeff 0)) ?_
    have hev : p.eval (-(g.coeff 0)) = 0 := by rw [hf, hg.eq_X_add_C hgd]; simp
    rw [hp] at hev
    simpa using hev
  · have hgf := hg.eq_X_sq_add hgd
    have hff := hfm.eq_X_sq_add (by omega)
    have key : (X ^ 4 + C (g.coeff 1 + f.coeff 1) * X ^ 3
        + C (g.coeff 0 + f.coeff 0 + g.coeff 1 * f.coeff 1) * X ^ 2
        + C (g.coeff 1 * f.coeff 0 + g.coeff 0 * f.coeff 1) * X
        + C (g.coeff 0 * f.coeff 0) : R[X]) = p := by
      rw [← quartic_expand, ← hgf, ← hff, ← hf]
    rw [hp] at key
    exact h2 (g.coeff 1) (g.coeff 0) (f.coeff 1) (f.coeff 0) (quartic_coeff key)

/-- A monic quintic with no root and no monic quadratic factor is irreducible: a proper factor
would have degree at most `5 / 2 = 2`. -/
theorem irreducible_quintic {p : R[X]} (c₄ c₃ c₂ c₁ c₀ : R)
    (hp : p = X ^ 5 + C c₄ * X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀)
    (h1 : ∀ x : R, x ^ 5 + c₄ * x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ ≠ 0)
    (h2 : ∀ a b c d e : R, ¬(a + c = c₄ ∧ b + d + a * c = c₃ ∧ e + a * d + b * c = c₂ ∧
      a * e + b * d = c₁ ∧ b * e = c₀)) :
    Irreducible p := by
  have hm : p.Monic := by rw [hp]; monicity!
  have hdeg : p.natDegree = 5 := by rw [hp]; compute_degree!
  have hne1 : p ≠ 1 := fun h => by simp [h] at hdeg
  rw [hm.irreducible_iff_lt_natDegree_lt hne1]
  rintro g hg hmem ⟨f, hf⟩
  rw [Finset.mem_Ioc, hdeg] at hmem
  have hfm : f.Monic := hg.of_mul_monic_left (hf ▸ hm)
  have hsum : g.natDegree + f.natDegree = 5 := by
    rw [← hdeg, hf, hg.natDegree_mul hfm]
  obtain hgd | hgd : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
  · refine h1 (-(g.coeff 0)) ?_
    have hev : p.eval (-(g.coeff 0)) = 0 := by rw [hf, hg.eq_X_add_C hgd]; simp
    rw [hp] at hev
    simpa using hev
  · have hgf := hg.eq_X_sq_add hgd
    have hff := hfm.eq_X_cube_add (by omega)
    have key : (X ^ 5 + C (g.coeff 1 + f.coeff 2) * X ^ 4
        + C (g.coeff 0 + f.coeff 1 + g.coeff 1 * f.coeff 2) * X ^ 3
        + C (f.coeff 0 + g.coeff 1 * f.coeff 1 + g.coeff 0 * f.coeff 2) * X ^ 2
        + C (g.coeff 1 * f.coeff 0 + g.coeff 0 * f.coeff 1) * X
        + C (g.coeff 0 * f.coeff 0) : R[X]) = p := by
      rw [← quintic_expand, ← hgf, ← hff, ← hf]
    rw [hp] at key
    exact h2 (g.coeff 1) (g.coeff 0) (f.coeff 2) (f.coeff 1) (f.coeff 0) (quintic_coeff key)

/-- An integer quartic is irreducible as soon as its reduction modulo some prime is: both
hypotheses are then finite, so each is a `decide`. -/
theorem irreducible_quartic_int {p : ℤ[X]} (c₃ c₂ c₁ c₀ : ℤ) (m : ℕ) [Fact (Nat.Prime m)]
    (hp : p = X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀)
    (h1 : ∀ x : ZMod m, x ^ 4 + (c₃ : ZMod m) * x ^ 3 + (c₂ : ZMod m) * x ^ 2
      + (c₁ : ZMod m) * x + (c₀ : ZMod m) ≠ 0)
    (h2 : ∀ a b c d : ZMod m, ¬(a + c = (c₃ : ZMod m) ∧ b + d + a * c = (c₂ : ZMod m) ∧
      a * d + b * c = (c₁ : ZMod m) ∧ b * d = (c₀ : ZMod m))) :
    Irreducible p := by
  refine Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod m)) p
    (by rw [hp]; monicity!) ?_
  refine irreducible_quartic (c₃ : ZMod m) (c₂ : ZMod m) (c₁ : ZMod m) (c₀ : ZMod m) ?_ h1 h2
  rw [hp]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

/-- An integer quintic is irreducible as soon as its reduction modulo some prime is. -/
theorem irreducible_quintic_int {p : ℤ[X]} (c₄ c₃ c₂ c₁ c₀ : ℤ) (m : ℕ) [Fact (Nat.Prime m)]
    (hp : p = X ^ 5 + C c₄ * X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀)
    (h1 : ∀ x : ZMod m, x ^ 5 + (c₄ : ZMod m) * x ^ 4 + (c₃ : ZMod m) * x ^ 3
      + (c₂ : ZMod m) * x ^ 2 + (c₁ : ZMod m) * x + (c₀ : ZMod m) ≠ 0)
    (h2 : ∀ a b c d e : ZMod m, ¬(a + c = (c₄ : ZMod m) ∧ b + d + a * c = (c₃ : ZMod m) ∧
      e + a * d + b * c = (c₂ : ZMod m) ∧ a * e + b * d = (c₁ : ZMod m) ∧
      b * e = (c₀ : ZMod m))) :
    Irreducible p := by
  refine Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod m)) p
    (by rw [hp]; monicity!) ?_
  refine irreducible_quintic (c₄ : ZMod m) (c₃ : ZMod m) (c₂ : ZMod m) (c₁ : ZMod m)
    (c₀ : ZMod m) ?_ h1 h2
  rw [hp]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

end Polynomial
