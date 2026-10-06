import equational_theories.Spectrum.Equation667FiberThreePeriodTwo
import equational_theories.Spectrum.Equation667EightClassification.Certificate
import equational_theories.Spectrum.Equation667SimpleTwelve

/-! No three-element-fiber extension of the idempotent-free eight-point
E667 quasigroup. Only a handful of coefficient identities are needed. -/
namespace Spectrum.E667.FiberEight
abbrev K := Eight.K
abbrev F := ZMod 3
abbrev quotient := Eight.quotient

def s (i : K) : K := quotient i i
def t (i j : K) : K := quotient (s i) j
def u (i j : K) : K := quotient i (t i j)

/-- The eight-point quotient has a two-cycle under squaring, so the
classification-independent three-fiber obstruction applies. -/
theorem no_signs (A B : K → K → F)
    (hA : ∀ i j, A i j ≠ 0) (hB : ∀ i j, B i j ≠ 0)
    (hc : ∀ i j,
      B j (u i j) * (A i (t i j) + B i (t i j) * A (s i) j * (A i i + B i i)) = 1 ∧
      A j (u i j) + B j (u i j) * B i (t i j) * B (s i) j = 0) : False := by
  exact FiberThreePeriodTwo.no_signs quotient (by decide +kernel)
    0 (by decide +kernel) A B hA hB hc

def fiberOp (A B C : K → K → F) (x y : K × F) : K × F :=
  (quotient x.1 y.1, A x.1 y.1 * x.2 + B x.1 y.1 * y.2 + C x.1 y.1)

/-- Evaluating the law at three points extracts its two linear coefficients.
The constants are arbitrary, and cancel from both equations. -/
theorem coefficients (A B C : K → K → F)
    (h : @Equation667 (K × F) ⟨fiberOp A B C⟩) (i j : K) :
    B j (u i j) * (A i (t i j) + B i (t i j) * A (s i) j * (A i i + B i i)) = 1 ∧
    A j (u i j) + B j (u i j) * B i (t i j) * B (s i) j = 0 := by
  have h0 := congrArg Prod.snd ((h (i, 0) (j, 0)).symm)
  have hx := congrArg Prod.snd ((h (i, 1) (j, 0)).symm)
  have hy := congrArg Prod.snd ((h (i, 0) (j, 1)).symm)
  dsimp only [Magma.op, fiberOp] at h0 hx hy
  dsimp only [s, t, u]
  constructor
  · linear_combination hx - h0
  · linear_combination hy - h0

/-- There is no E667 extension over this quotient with arbitrary affine
Latin three-point blocks. Every Latin operation on three points has this
form; the coefficients may vary independently from block to block. -/
theorem no_affine_fiber_extension (A B C : K → K → F)
    (hA : ∀ i j, A i j ≠ 0) (hB : ∀ i j, B i j ≠ 0) :
    ¬ @Equation667 (K × F) ⟨fiberOp A B C⟩ := by
  intro h
  exact no_signs A B hA hB (coefficients A B C h)

def generalFiberOp (g : K → K → F → F → F) (x y : K × F) : K × F :=
  (quotient x.1 y.1, g x.1 y.1 x.2 y.2)

/-- No extension by three-element fibers exists, even when every block is
an arbitrary Latin operation. Coefficients and origins need not be shared
between distinct blocks. -/
theorem no_latin_fiber_extension (g : K → K → F → F → F)
    (hL : ∀ i j x, Function.Injective (g i j x))
    (hR : ∀ i j y, Function.Injective (fun x => g i j x y)) :
    ¬ @Equation667 (K × F) ⟨generalFiberOp g⟩ := by
  let A := fun i j => g i j 1 0 - g i j 0 0
  let B := fun i j => g i j 0 1 - g i j 0 0
  let C := fun i j => g i j 0 0
  have hA (i j) : A i j ≠ 0 := by
    intro he
    exact (by decide +kernel : (1 : F) ≠ 0) (hR i j 0 (sub_eq_zero.mp he))
  have hB (i j) : B i j ≠ 0 := by
    intro he
    exact (by decide +kernel : (1 : F) ≠ 0) (hL i j 0 (sub_eq_zero.mp he))
  have hop : generalFiberOp g = fiberOp A B C := by
    funext x y
    apply Prod.ext
    · rfl
    · exact FiberThree.latin_three_affine (g x.1 y.1) (hL x.1 y.1) (hR x.1 y.1) x.2 y.2
  rw [hop]
  exact no_affine_fiber_extension A B C hA hB

/-- Finiteness makes every block Latin, so no additional Latin hypotheses
are needed for the final obstruction. -/
theorem no_fiber_extension (g : K → K → F → F → F) :
    ¬ @Equation667 (K × F) ⟨generalFiberOp g⟩ := by
  intro h
  letI : Magma (K × F) := ⟨generalFiberOp g⟩
  apply no_latin_fiber_extension g ?_ ?_ h
  · intro i j x a b he
    have hp : (i, x) ◇ (j, a) = (i, x) ◇ (j, b) := by
      exact Prod.ext rfl he
    exact congrArg Prod.snd (E667883.left_injective667 h (i, x) hp)
  · intro i j y a b he
    have hp : (i, a) ◇ (j, y) = (i, b) ◇ (j, y) := by
      exact Prod.ext rfl he
    exact congrArg Prod.snd (E667883.right_injective667 h (j, y) hp)

/-- An arbitrary twenty-four-element E667 model cannot map onto this eight-point
quotient. Equal fiber cardinalities justify choosing the three-point labels
used by the coefficient argument. -/
theorem no_quotient_canonical {A : Type*} [Magma A] [Finite A]
    (hA : Equation667 A) (hc : Nat.card A = 24)
    (π : A → K) (surj : Function.Surjective π)
    (hom : ∀ x y, π (x ◇ y) = quotient (π x) (π y)) : False := by
  classical
  letI : Magma K := ⟨quotient⟩
  have hK : Equation667 K := by decide +kernel
  have hf (b : K) : Nat.card {x : A // π x = b} = 3 := by
    have hh := Quotients.card_eq_mul_fiber hA hK π hom surj b
    rw [hc] at hh
    norm_num [K] at hh
    omega
  exact FiberThreePeriodTwo.no_quotient hA hK π hom hf 0 (by decide +kernel)


spectrum_assert no_fiber_extension complete
spectrum_assert no_quotient_canonical complete
end Spectrum.E667.FiberEight
