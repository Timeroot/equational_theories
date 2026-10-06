import equational_theories.Spectrum.Equation667FiberThree

/-! An E667 quasigroup cannot have three-element fibers over a quotient
whose squaring map has a point of period one or two. The obstruction uses
only coefficient signs in F₃, and no classification of the quotient. -/
namespace Spectrum.E667.FiberThreePeriodTwo
abbrev F := ZMod 3
variable {K : Type*} (quotient : K → K → K)

def s (i : K) : K := quotient i i
def t (i j : K) : K := quotient (s quotient i) j
def u (i j : K) : K := quotient i (t quotient i j)

private theorem square_one (a : F) (ha : a ≠ 0) : a ^ 2 = 1 := by
  exact (by decide +kernel : ∀ z : F, z ≠ 0 → z ^ 2 = 1) a ha

/-- When the diagonal signs agree, the first coefficient also fixes the
product of the other four signs. This is a six-sign calculation in F₃. -/
private theorem third_sign (a b c d e f : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (hab : a * b = 1)
    (h : f * (c + d * e * (a + b)) = 1) : a * d * e * f = 1 := by
  revert ha hb hc hd he hf hab h
  revert a b c d e f
  set_option synthInstance.maxSize 1000 in decide +kernel

/-- Two pairs of sign identities fix the diagonal products at a square cycle.
Five further identities multiply to `1 = -1`. -/
theorem no_signs
    (hq : ∀ i j, quotient j (quotient i (quotient (quotient i i) j)) = i)
    (a : K) (hperiod : quotient (quotient a a) (quotient a a) = a) (A B : K → K → F)
    (hA : ∀ i j, A i j ≠ 0) (hB : ∀ i j, B i j ≠ 0)
    (hc : ∀ i j,
      B j (u quotient i j) * (A i (t quotient i j) + B i (t quotient i j) * A (s quotient i) j * (A i i + B i i)) = 1 ∧
      A j (u quotient i j) + B j (u quotient i j) * B i (t quotient i j) * B (s quotient i) j = 0) : False := by
  have hsqA (i j) := square_one (A i j) (hA i j)
  have hsqB (i j) := square_one (B i j) (hB i j)
  have cube (a : F) : a ^ 3 = a := by
    exact (by decide +kernel : ∀ z : F, z ^ 3 = z) a
  have first (i j) : A i (t quotient i j) * B j (u quotient i j) * A i i * B i i = -1 := by
    have hh := FiberThree.first_coefficient_sign (A i i) (B i i) (A i (t quotient i j))
      (B i (t quotient i j)) (A (s quotient i) j) (B j (u quotient i j))
      (hA _ _) (hB _ _) (hA _ _) (hB _ _) (hA _ _) (hB _ _) (hc i j).1
    calc
      _ = -(A i i * B i i) * A i i * B i i := by rw [hh]
      _ = -(A i i ^ 2 * B i i ^ 2) := by ring
      _ = -1 := by rw [hsqA, hsqB]; norm_num
  have second (i j) :
      A j (u quotient i j) * B j (u quotient i j) * B i (t quotient i j) * B (s quotient i) j = -1 := by
    have hh := (hc i j).2
    have hs := hsqA j (u quotient i j)
    linear_combination A j (u quotient i j) * hh - hs
  let b := quotient a a
  let c := quotient a b
  let d := quotient b c
  have haa : quotient a a = b := rfl
  have hbb : quotient b b = a := hperiod
  have hab : quotient a b = c := rfl
  have hbc : quotient b c = d := rfl
  have hbd : quotient b d = b := by
    simpa only [hbb, hab, hbc] using hq b b
  have ht_ab : t quotient a b = a := hbb
  have hu_ab : u quotient a b = b := by rw [u, ht_ab, haa]
  have ht_ba : t quotient b a = b := by simp only [t, s, hbb, haa]
  have hu_ba : u quotient b a = a := by rw [u, ht_ba, hbb]
  have ht_ad : t quotient a d = b := hbd
  have hu_ad : u quotient a d = c := by rw [u, ht_ad, hab]
  have ht_bb : t quotient b b = c := by simp only [t, s, hbb, hab]
  have hu_bb : u quotient b b = d := by rw [u, ht_bb, hbc]
  have h0 := first a b
  have h1 := second b a
  have h2 := second a b
  rw [ht_ab, hu_ab] at h0 h2
  rw [ht_ba, hu_ba] at h1
  rw [s, hbb] at h1
  change A b b * B b b * B a a * B b b = -1 at h2
  have diag0 : A a a * B a a = 1 := by
    have hp := congrArg₂ (· * ·) h0 h1
    ring_nf at hp
    simp only [hsqB, cube, mul_one] at hp
    exact hp
  have diag1 : A b b * B b b = 1 := by
    have hp := congrArg₂ (· * ·) h0 h2
    ring_nf at hp
    simpa only [hsqA, hsqB, cube, one_mul, mul_one, mul_comm] using hp
  have third (i j) (hd : A i i * B i i = 1) :
      A i i * B i (t quotient i j) * A (s quotient i) j * B j (u quotient i j) = 1 :=
    third_sign _ _ _ _ _ _ (hA _ _) (hB _ _) (hA _ _) (hB _ _)
      (hA _ _) (hB _ _) hd (hc i j).1
  have h3 := first a d
  have h4 := second b b
  have h5 := third a d diag0
  have h6 := third b b diag1
  rw [ht_ad, hu_ad] at h3 h5
  rw [ht_bb, hu_bb] at h4 h6
  rw [s, hbb] at h4
  change A a a * B a b * A b d * B d c = 1 at h5
  rw [s, hbb] at h6
  have hp := congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) h2 h3) h4) h5) h6
  ring_nf at hp
  simp only [hsqA, hsqB, mul_one] at hp
  exact (by decide +kernel : (1 : F) ≠ -1) hp

def fiberOp (A B C : K → K → F) (x y : K × F) : K × F :=
  (quotient x.1 y.1, A x.1 y.1 * x.2 + B x.1 y.1 * y.2 + C x.1 y.1)

/-- Evaluating the law at three points extracts its two linear coefficients.
The constants are arbitrary, and cancel from both equations. -/
theorem coefficients (A B C : K → K → F)
    (h : @Equation667 (K × F) ⟨fiberOp quotient A B C⟩) (i j : K) :
    B j (u quotient i j) * (A i (t quotient i j) + B i (t quotient i j) * A (s quotient i) j * (A i i + B i i)) = 1 ∧
    A j (u quotient i j) + B j (u quotient i j) * B i (t quotient i j) * B (s quotient i) j = 0 := by
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
theorem no_affine_fiber_extension
    (hq : ∀ i j, quotient j (quotient i (quotient (quotient i i) j)) = i)
    (a : K) (hperiod : quotient (quotient a a) (quotient a a) = a) (A B C : K → K → F)
    (hA : ∀ i j, A i j ≠ 0) (hB : ∀ i j, B i j ≠ 0) :
    ¬ @Equation667 (K × F) ⟨fiberOp quotient A B C⟩ := by
  intro h
  exact no_signs quotient hq a hperiod A B hA hB (coefficients quotient A B C h)

def generalFiberOp (g : K → K → F → F → F) (x y : K × F) : K × F :=
  (quotient x.1 y.1, g x.1 y.1 x.2 y.2)

/-- No extension by three-element fibers exists, even when every block is
an arbitrary Latin operation. Coefficients and origins need not be shared
between distinct blocks. -/
theorem no_latin_fiber_extension
    (hq : ∀ i j, quotient j (quotient i (quotient (quotient i i) j)) = i)
    (a : K) (hperiod : quotient (quotient a a) (quotient a a) = a) (g : K → K → F → F → F)
    (hL : ∀ i j x, Function.Injective (g i j x))
    (hR : ∀ i j y, Function.Injective (fun x => g i j x y)) :
    ¬ @Equation667 (K × F) ⟨generalFiberOp quotient g⟩ := by
  let A := fun i j => g i j 1 0 - g i j 0 0
  let B := fun i j => g i j 0 1 - g i j 0 0
  let C := fun i j => g i j 0 0
  have hA (i j) : A i j ≠ 0 := by
    intro he
    exact (by decide +kernel : (1 : F) ≠ 0) (hR i j 0 (sub_eq_zero.mp he))
  have hB (i j) : B i j ≠ 0 := by
    intro he
    exact (by decide +kernel : (1 : F) ≠ 0) (hL i j 0 (sub_eq_zero.mp he))
  have hop : generalFiberOp quotient g = fiberOp quotient A B C := by
    funext x y
    apply Prod.ext
    · rfl
    · exact FiberThree.latin_three_affine (g x.1 y.1) (hL x.1 y.1) (hR x.1 y.1) x.2 y.2
  rw [hop]
  exact no_affine_fiber_extension quotient hq a hperiod A B C hA hB

/-- Finiteness makes every block Latin, so no additional Latin hypotheses
are needed for the final obstruction. -/
theorem no_fiber_extension [Finite K]
    (hq : ∀ i j, quotient j (quotient i (quotient (quotient i i) j)) = i)
    (a : K) (hperiod : quotient (quotient a a) (quotient a a) = a) (g : K → K → F → F → F) :
    ¬ @Equation667 (K × F) ⟨generalFiberOp quotient g⟩ := by
  intro h
  letI : Magma (K × F) := ⟨generalFiberOp quotient g⟩
  apply no_latin_fiber_extension quotient hq a hperiod g ?_ ?_ h
  · intro i j x a b he
    have hp : (i, x) ◇ (j, a) = (i, x) ◇ (j, b) := by
      exact Prod.ext rfl he
    exact congrArg Prod.snd (E667883.left_injective667 h (i, x) hp)
  · intro i j y a b he
    have hp : (i, a) ◇ (j, y) = (i, b) ◇ (j, y) := by
      exact Prod.ext rfl he
    exact congrArg Prod.snd (E667883.right_injective667 h (j, y) hp)


/-- Coordinate-free form: a finite E667 magma cannot map onto a quotient
with three-point fibers and a square cycle of length one or two. -/
theorem no_quotient {X K : Type*} [Magma X] [Finite X] [Magma K] [Finite K]
    (hX : Equation667 X) (hK : Equation667 K)
    (π : X → K) (hom : ∀ x y, π (x ◇ y) = π x ◇ π y)
    (hf : ∀ b : K, Nat.card {x : X // π x = b} = 3)
    (a : K) (hperiod : (a ◇ a) ◇ (a ◇ a) = a) : False := by
  classical
  let q : K → K → K := fun x y => x ◇ y
  letI (b : K) : Fintype {x : X // π x = b} := Fintype.ofFinite _
  let ef (b : K) : {x : X // π x = b} ≃ F :=
    Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hf b)
  let E : X ≃ K × F := (Equiv.sigmaFiberEquiv π).symm.trans
    (Equiv.sigmaEquivProdOfEquiv ef)
  have ep (a : X) : (E a).1 = π a := rfl
  have eps (z : K × F) : π (E.symm z) = z.1 := by
    rw [← ep, E.apply_symm_apply]
  let M : Magma (K × F) := (inferInstance : Magma X).relabel E
  let g : K → K → F → F → F := fun i j a b => (M.op (i, a) (j, b)).2
  have hop : M.op = generalFiberOp q g := by
    funext x y
    apply Prod.ext
    · change (E (E.symm x ◇ E.symm y)).1 = q x.1 y.1
      rw [ep, hom, eps, eps]
    · rfl
  have back (x y : K × F) : E.symm (M.op x y) = E.symm x ◇ E.symm y := by
    change E.symm (E (E.symm x ◇ E.symm y)) = E.symm x ◇ E.symm y
    exact E.symm_apply_apply _
  have hm : @Equation667 (K × F) M := by
    intro x y
    apply E.symm.injective
    simpa only [back] using hX (E.symm x) (E.symm y)
  apply no_fiber_extension q (fun i j => (hK i j).symm) a hperiod g
  intro x y
  have hh := hm x y
  change x = M.op y (M.op x (M.op (M.op x x) y)) at hh
  simpa only [hop] using hh


spectrum_assert no_quotient complete
spectrum_assert no_fiber_extension complete
end Spectrum.E667.FiberThreePeriodTwo
