import equational_theories.Spectrum.Equation667ConstantDiagonal
import equational_theories.Spectrum.Equation667Quotients
import Mathlib.Data.ZMod.Basic

/-! A small coefficient obstruction to three-point-fiber extensions of
the idempotent-free five-element E667 quasigroup. -/

namespace Spectrum.E667.FiberThree

abbrev K := Fin 5
abbrev F := ZMod 3

def quotient (i j : K) : K :=
  ⟨(3 * i.val + 3 * j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩

def s (i : K) : K := quotient i i
def t (i j : K) : K := quotient (s i) j
def u (i j : K) : K := quotient i (t i j)

private theorem square_one (a : F) (ha : a ≠ 0) : a ^ 2 = 1 := by
  exact (by decide +kernel : ∀ z : F, z ≠ 0 → z ^ 2 = 1) a ha

/-- The coefficient of the first variable forces a sign equality. This is
only a six-sign calculation over the three-element field. -/
theorem first_coefficient_sign (a b c d e f : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (h : f * (c + d * e * (a + b)) = 1) : c * f = -(a * b) := by
  revert ha hb hc hd he hf h
  revert a b c d e f
  set_option synthInstance.maxSize 1000 in
    decide +kernel

/-- The sign equations obtained from the two coefficients have no solution.
Multiply fifteen instances: every sign occurs exactly twice on the left,
whereas the right is minus one. -/
theorem no_signs (A B : K → K → F)
    (hA : ∀ i j, A i j ≠ 0) (hB : ∀ i j, B i j ≠ 0)
    (hfirst : ∀ i j,
      A i (t i j) * B j (u i j) = -(A i i * B i i))
    (hsecond : ∀ i j,
      A j (u i j) * B j (u i j) * B i (t i j) * B (s i) j = -1) : False := by
  have hsqA (i j) := square_one (A i j) (hA i j)
  have hsqB (i j) := square_one (B i j) (hB i j)
  have hfirst' (i j) :
      A i (t i j) * B j (u i j) * A i i * B i i = -1 := by
    rw [hfirst]
    calc
      -(A i i * B i i) * A i i * B i i = -(A i i ^ 2 * B i i ^ 2) := by ring
      _ = -1 := by rw [hsqA, hsqB]; norm_num
  have h0 := hfirst' (0 : K) (1 : K)
  have h1 := hfirst' (1 : K) (2 : K)
  have h2 := hfirst' (2 : K) (3 : K)
  have h3 := hfirst' (3 : K) (4 : K)
  have h4 := hfirst' (4 : K) (0 : K)
  have h5 := hsecond (0 : K) (3 : K)
  have h6 := hsecond (1 : K) (4 : K)
  have h7 := hsecond (2 : K) (0 : K)
  have h8 := hsecond (3 : K) (1 : K)
  have h9 := hsecond (4 : K) (2 : K)
  have h10 := hsecond (0 : K) (4 : K)
  have h11 := hsecond (1 : K) (0 : K)
  have h12 := hsecond (2 : K) (1 : K)
  have h13 := hsecond (3 : K) (2 : K)
  have h14 := hsecond (4 : K) (3 : K)
  change A 0 2 * B 1 2 * A 0 0 * B 0 0 = -1 at h0
  change A 1 3 * B 2 3 * A 1 1 * B 1 1 = -1 at h1
  change A 2 4 * B 3 4 * A 2 2 * B 2 2 = -1 at h2
  change A 3 0 * B 4 0 * A 3 3 * B 3 3 = -1 at h3
  change A 4 1 * B 0 1 * A 4 4 * B 4 4 = -1 at h4
  change A 3 0 * B 3 0 * B 0 3 * B 1 3 = -1 at h5
  change A 4 1 * B 4 1 * B 1 4 * B 2 4 = -1 at h6
  change A 0 2 * B 0 2 * B 2 0 * B 3 0 = -1 at h7
  change A 1 3 * B 1 3 * B 3 1 * B 4 1 = -1 at h8
  change A 2 4 * B 2 4 * B 4 2 * B 0 2 = -1 at h9
  change A 4 4 * B 4 4 * B 0 1 * B 1 4 = -1 at h10
  change A 0 0 * B 0 0 * B 1 2 * B 2 0 = -1 at h11
  change A 1 1 * B 1 1 * B 2 3 * B 3 1 = -1 at h12
  change A 2 2 * B 2 2 * B 3 4 * B 4 2 = -1 at h13
  change A 3 3 * B 3 3 * B 4 0 * B 0 3 = -1 at h14
  have hp := (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14)
  ring_nf at hp
  simp only [hsqA, hsqB, mul_one] at hp
  exact (by decide +kernel : (1 : F) ≠ -1) hp

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
  apply no_signs A B hA hB
  · intro i j
    exact first_coefficient_sign (A i i) (B i i) (A i (t i j))
      (B i (t i j)) (A (s i) j) (B j (u i j))
      (hA _ _) (hB _ _) (hA _ _) (hB _ _) (hA _ _) (hB _ _)
      (coefficients A B C h i j).1
  · intro i j
    have hh := (coefficients A B C h i j).2
    have hs := square_one (A j (u i j)) (hA _ _)
    linear_combination A j (u i j) * hh - hs

private theorem affine_permutation (f : F → F) (hf : Function.Injective f) (x : F) :
    f x = (f 1 - f 0) * x + f 0 := by
  exact (by decide +kernel : ∀ f : F → F, Function.Injective f →
    ∀ x, f x = (f 1 - f 0) * x + f 0) f hf x

/-- Every Latin operation on three points is affine. Only the elementary
27-function fact about permutations of three points is checked finitely;
the two-variable assertion follows by comparing its row and column slopes. -/
theorem latin_three_affine (f : F → F → F)
    (hL : ∀ x, Function.Injective (f x))
    (hR : ∀ y, Function.Injective (fun x => f x y)) (x y : F) :
    f x y = (f 1 0 - f 0 0) * x + (f 0 1 - f 0 0) * y + f 0 0 := by
  let D := f 1 1 - f 1 0 - f 0 1 + f 0 0
  let A := f 1 0 - f 0 0
  let B := f 0 1 - f 0 0
  have form (x y : F) : f x y = D * x * y + A * x + B * y + f 0 0 := by
    have hc := affine_permutation (fun z => f z y) (hR y) x
    have h0 := affine_permutation (f 0) (hL 0) y
    have h1 := affine_permutation (f 1) (hL 1) y
    dsimp [D, A, B]
    linear_combination hc + x * h1 + (1 - x) * h0
  have slopes (x : F) : D * x + B ≠ 0 := by
    intro he
    have hh : f x 1 = f x 0 := by
      rw [form x 1, form x 0]
      linear_combination he
    exact (by decide +kernel : (1 : F) ≠ 0) (hL x hh)
  have hd : D = 0 :=
    (by decide +kernel : ∀ d b : F, (∀ z : F, d * z + b ≠ 0) → d = 0) D B slopes
  simpa only [hd, zero_mul, zero_add] using form x y

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
    · exact latin_three_affine (g x.1 y.1) (hL x.1 y.1) (hR x.1 y.1) x.2 y.2
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

/-- An arbitrary fifteen-element E667 model cannot map onto this five-point
quotient. Equal fiber cardinalities justify choosing the three-point labels
used by the coefficient argument. -/
theorem no_quotient_five {A : Type*} [Magma A] [Finite A]
    (hA : Equation667 A) (hc : Nat.card A = 15)
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
  letI (b : K) : Fintype {x : A // π x = b} := Fintype.ofFinite _
  let ef (b : K) : {x : A // π x = b} ≃ F :=
    Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hf b)
  let E : A ≃ K × F := (Equiv.sigmaFiberEquiv π).symm.trans
    (Equiv.sigmaEquivProdOfEquiv ef)
  have ep (a : A) : (E a).1 = π a := rfl
  have eps (z : K × F) : π (E.symm z) = z.1 := by
    rw [← ep, E.apply_symm_apply]
  let M : Magma (K × F) := (inferInstance : Magma A).relabel E
  let g : K → K → F → F → F := fun i j a b => (M.op (i, a) (j, b)).2
  have hop : M.op = generalFiberOp g := by
    funext x y
    apply Prod.ext
    · change (E (E.symm x ◇ E.symm y)).1 = quotient x.1 y.1
      rw [ep, hom, eps, eps]
    · rfl
  have back (x y : K × F) : E.symm (M.op x y) = E.symm x ◇ E.symm y := by
    change E.symm (E (E.symm x ◇ E.symm y)) = E.symm x ◇ E.symm y
    exact E.symm_apply_apply _
  have hm : @Equation667 (K × F) M := by
    intro x y
    apply E.symm.injective
    simpa only [back] using hA (E.symm x) (E.symm y)
  apply no_fiber_extension g
  intro x y
  have hh := hm x y
  change x = M.op y (M.op x (M.op (M.op x x) y)) at hh
  simpa only [hop] using hh

spectrum_assert no_fiber_extension complete
spectrum_assert no_quotient_five complete

end Spectrum.E667.FiberThree
