import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import equational_theories.Definability.LinearTargets

/-!
# Linear magmas over the Gaussian integers

Three linear models `x ◇ y = a * x + b * y` over `ℤ[i]`, the largest single block of the
definability board that one ring settles. Their targets are handled once and for all by
`Definability/LinearTargets.lean`, which reduces a refutation over a domain to three arithmetic
facts about the ring:

* `hc`, that `1 + c * x` never vanishes, where `c = a + b - 1` is the coefficient modulus;
* `hP`, that an explicit univariate polynomial has no root;
* `h₃`, that `3 + c * x` never vanishes, for the one target that needs it.

Each is one reduction to a residue field. `hP` always goes to `𝔽₂ = ℤ[i] / (1 + i)`, where all six
polynomials the board asks about are irreducible or constant; `hc` goes to the residue field of the
prime `c` itself, which is `𝔽₅` for the first two models and `𝔽₁₃` for the third.

That `hP` needs a residue field of *odd* characteristic to fail — and it does fail in every finite
quotient of `ℤ[i]`, since a cubic over a large enough finite field always has a root — is why these
models have no `ZMod` replacement and have to be written by hand.

The certificates refute `TermDefinableFrom`, and only over all magmas: the witness is infinite, and
a clone argument bounds terms rather than formulas.
-/

open Law Law.MagmaLaw

namespace Magma

local notation "ℤ[i]" => GaussianInt

/-! ### The ring -/

/-- `i`, the square root of `-1` in the Gaussian integers. -/
def gi : ℤ[i] := ⟨0, 1⟩

theorem gi_sq : gi * gi = -1 := by decide

/-- Reduction at the ramified prime `1 + i` above `2`, which sends `i` to `1`. -/
def gi2 : ℤ[i] →+* ZMod 2 := Zsqrtd.lift ⟨1, by decide⟩

/-- Reduction at the prime `2 + i` above `5`, which sends `i` to `3`. -/
def gi5a : ℤ[i] →+* ZMod 5 := Zsqrtd.lift ⟨3, by decide⟩

/-- Reduction at the prime `1 + 2 * i` above `5`, which sends `i` to `2`. -/
def gi5b : ℤ[i] →+* ZMod 5 := Zsqrtd.lift ⟨2, by decide⟩

/-- Reduction at the prime `2 + 3 * i` above `13`, which sends `i` to `8`. -/
def gi13 : ℤ[i] →+* ZMod 13 := Zsqrtd.lift ⟨8, by decide⟩

/-- If `φ` kills `c` but not `n`, then `n` is not in the ideal `(c)`, so `n + c * x` never
vanishes. This is how a coefficient modulus is shown not to be a unit, and how the extra factor
`3` of `Equation3472` is shown to be prime to it. -/
theorem gi_add_mul_ne_zero {S : Type} [CommRing S] (φ : ℤ[i] →+* S) (n c : ℤ[i])
    (hc : φ c = 0) (hn : φ n ≠ 0) (x : ℤ[i]) : n + c * x ≠ 0 := by
  intro h
  refine hn ?_
  have h' := congrArg φ h
  rwa [map_add, map_mul, hc, zero_mul, add_zero, map_zero] at h'

/-! ### The polynomials, over `𝔽₂` -/

theorem gi_ne_3269 (x : ℤ[i]) : x ^ 3 - 3 * x ^ 2 + 2 * x - 1 ≠ 0 := by
  intro h
  have h2 := congrArg gi2 h
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, map_zero] at h2
  revert h2
  generalize gi2 x = y
  revert y
  decide

theorem gi_ne_3279 (x : ℤ[i]) : x ^ 3 - 2 * x ^ 2 + x - 1 ≠ 0 := by
  intro h
  have h2 := congrArg gi2 h
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, map_zero] at h2
  revert h2
  generalize gi2 x = y
  revert y
  decide

theorem gi_ne_3475 (x : ℤ[i]) : x ^ 3 - x ^ 2 + 1 ≠ 0 := by
  intro h
  have h2 := congrArg gi2 h
  simp only [map_sub, map_add, map_pow, map_one, map_zero] at h2
  revert h2
  generalize gi2 x = y
  revert y
  decide

theorem gi_ne_3675 (x : ℤ[i]) : 2 * x ^ 2 - 2 * x + 1 ≠ 0 := by
  intro h
  have h2 := congrArg gi2 h
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, map_zero] at h2
  revert h2
  generalize gi2 x = y
  revert y
  decide

theorem gi_ne_3472 (x : ℤ[i]) : x ^ 2 - x + 1 ≠ 0 := by
  intro h
  have h2 := congrArg gi2 h
  simp only [map_sub, map_add, map_pow, map_one, map_zero] at h2
  revert h2
  generalize gi2 x = y
  revert y
  decide

theorem gi_ne_quad (x : ℤ[i]) : x ^ 2 + 3 * x + 1 ≠ 0 := by
  intro h
  have h2 := congrArg gi2 h
  simp only [map_add, map_mul, map_pow, map_one, map_ofNat, map_zero] at h2
  revert h2
  generalize gi2 x = y
  revert y
  decide

/-! ### Model A: `x ◇ y = -x - i * y`

Coefficient sum `-1 - i`, so the modulus is `c = -2 - i`, the prime above `5` that `gi5a` kills.
-/

theorem giA_hc (x : ℤ[i]) : (1 : ℤ[i]) + (-2 - gi) * x ≠ 0 :=
  gi_add_mul_ne_zero gi5a 1 (-2 - gi) (by decide) (by decide) x

/-- Equation `546`, `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`, holds in model A. Two of the four
multiplications produce an `i ^ 2`, so this is not `ring` but one use of `Magma.gi_sq`. -/
theorem giA_satisfies_546 : @Equation546 ℤ[i] (lin (-1) (-gi)) := by
  intro x y z
  simp only [lin_op]
  linear_combination (-(gi ^ 2) * y - gi * z + x + y) * gi_sq

/-! ### Model B: `x ◇ y = -i * x - i * y`

Coefficient sum `-2 * i`, so the modulus is `c = -1 - 2 * i`, the other prime above `5`.
-/

theorem giB_hc (x : ℤ[i]) : (1 : ℤ[i]) + (-1 - 2 * gi) * x ≠ 0 :=
  gi_add_mul_ne_zero gi5b 1 (-1 - 2 * gi) (by decide) (by decide) x

/-- Equation `556`, `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`, holds in model B. -/
theorem giB_satisfies_556 : @Equation556 ℤ[i] (lin (-gi) (-gi)) := by
  intro x y z
  simp only [lin_op]
  linear_combination (-(gi ^ 2) * x - gi ^ 2 * z + gi * y + x) * gi_sq

/-! ### Model C: `x ◇ y = (-1 - i) * x - 2 * i * y`

Coefficient sum `-1 - 3 * i`, so the modulus is `c = -2 - 3 * i`, a prime above `13`. Being prime
to `3`, it also supplies the extra factor `Equation3472` needs.
-/

theorem giC_hc (x : ℤ[i]) : (1 : ℤ[i]) + (-2 - 3 * gi) * x ≠ 0 :=
  gi_add_mul_ne_zero gi13 1 (-2 - 3 * gi) (by decide) (by decide) x

theorem giC_h3 (x : ℤ[i]) : (3 : ℤ[i]) + (-2 - 3 * gi) * x ≠ 0 :=
  gi_add_mul_ne_zero gi13 3 (-2 - 3 * gi) (by decide) (by decide) x

/-- Equation `4588`, `(x ◇ x) ◇ x = (y ◇ x) ◇ y`, holds in model C. -/
theorem giC_satisfies_4588 : @Equation4588 ℤ[i] (lin (-1 - gi) (-2 * gi)) := by
  intro x y
  simp only [lin_op]
  linear_combination (x - y) * gi_sq

end Magma
