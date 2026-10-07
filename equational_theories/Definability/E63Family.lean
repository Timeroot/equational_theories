import equational_theories.Equations.All
import equational_theories.Spectrum.Status
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Ring.Units
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-!
# Translation inverses in the E63 family

These lemmas isolate the finite-only step in the known equivalences between
E63, E73, E118, E125, and E1692. No finiteness assumption is used here.
The affine calculation allows arbitrary, initially noncommuting endomorphisms
of an abelian group. Such models cannot exploit a one-sided translation inverse.
-/

namespace E63Family

section Translations
variable {G : Type*} [Magma G]

theorem left_surjective_63 (h : Equation63 G) (y : G) :
    Function.Surjective (fun x => y ◇ x) :=
  fun x => ⟨x ◇ (x ◇ y), (h x y).symm⟩

theorem left_injective_1692 (h : Equation1692 G) (y : G) :
    Function.Injective (fun x => y ◇ x) := by
  intro a b hab
  change y ◇ a = y ◇ b at hab
  rw [h a y, hab, ← h b y]

/-- The missing cyclic rotation of E63 follows exactly when its left translations
are injective. This is automatic on finite carriers, but not on arbitrary ones. -/
theorem equation1692_iff_left_injective (h : Equation63 G) :
    Equation1692 G ↔ ∀ y : G, Function.Injective (fun x => y ◇ x) := by
  refine ⟨left_injective_1692, fun hi x y => hi y ?_⟩
  exact h (y ◇ x) y

theorem left_injective_125 (h : Equation125 G) (y : G) :
    Function.Injective (fun x => y ◇ x) := by
  intro a b hab
  change y ◇ a = y ◇ b at hab
  rw [h a y, hab, ← h b y]

theorem left_surjective_125 (h : Equation125 G) (y : G) :
    Function.Surjective (fun x => y ◇ x) :=
  fun x => ⟨(y ◇ x) ◇ y, (h x y).symm⟩

theorem rotate_125 (h : Equation125 G) (x y : G) :
    (y ◇ (y ◇ x)) ◇ y = x := by
  apply left_injective_125 h y
  exact (h (y ◇ x) y).symm

theorem equation73_of_125 (h : Equation125 G) : Equation73 G := by
  intro x y
  obtain ⟨a, rfl⟩ := left_surjective_125 h y x
  exact congrArg (fun z => y ◇ z) (h a y)

/-- E73 already supplies a right inverse of `L_y²`. Injectivity of `L_y`
is sufficient to recover E125, with the original operation. -/
theorem equation125_iff_left_injective (h : Equation73 G) :
    Equation125 G ↔ ∀ y : G, Function.Injective (fun x => y ◇ x) := by
  refine ⟨left_injective_125, fun hi x y => hi y ?_⟩
  exact h (y ◇ x) y

/-- The dual rotation needed for E118 follows from surjective right translations. -/
theorem equation222_iff_right_surjective (h : Equation118 G) :
    Equation222 G ↔ ∀ y : G, Function.Surjective (fun x => x ◇ y) := by
  refine ⟨fun he y x => ⟨y ◇ (x ◇ y), (he x y).symm⟩, fun hs x y => ?_⟩
  obtain ⟨a, rfl⟩ := hs y x
  exact congrArg (fun z => z ◇ y) (h a y)

/-- A concrete Mal'tsev term, written using the two term divisions of E125:
`p(x,y,z) = (x / (y\y)) * (y\z)`. -/
def malcev125 (x y z : G) : G :=
  let e := (y ◇ y) ◇ y
  (e ◇ (e ◇ x)) ◇ ((y ◇ z) ◇ y)

theorem malcev125_left (h : Equation125 G) (x y : G) :
    malcev125 x y y = x :=
  rotate_125 h x ((y ◇ y) ◇ y)

theorem malcev125_right (h : Equation125 G) (y z : G) :
    malcev125 y y z = z := by
  let e := (y ◇ y) ◇ y
  have he : y ◇ e = y := (h y y).symm
  have hdiv : e ◇ (e ◇ y) = y := by
    have hh := equation73_of_125 h y e
    rw [he] at hh
    exact hh.symm
  change (e ◇ (e ◇ y)) ◇ ((y ◇ z) ◇ y) = z
  rw [hdiv]
  exact (h z y).symm

end Translations

namespace Affine
section Ring
variable {R : Type*} [Ring R]

/-- The E63 coefficient identities force commuting units, in any unital ring. -/
theorem ring63 (A B : R)
    (h1 : B * A + B ^ 2 * A = 1) (h2 : A + B ^ 3 = 0) :
    Commute A B ∧ IsUnit A ∧ IsUnit B := by
  have ha : A = -B ^ 3 := eq_neg_of_add_eq_zero_left h2
  have hc : Commute A B := by rw [ha]; show -B ^ 3 * B = B * -B ^ 3; noncomm_ring
  have hba : (B + B ^ 2) * A = 1 := by
    linear_combination (norm := noncomm_ring) h1
  have hab : A * (B + B ^ 2) = 1 := by
    calc
      A * (B + B ^ 2) = (B + B ^ 2) * A := by rw [ha]; noncomm_ring
      _ = 1 := hba
  refine ⟨hc, isUnit_iff_exists.mpr ⟨B + B ^ 2, hab, hba⟩, ?_⟩
  have hb : B * -(B ^ 3 + B ^ 4) = 1 := by
    rw [ha] at h1
    linear_combination (norm := noncomm_ring) h1
  exact isUnit_iff_exists.mpr ⟨-(B ^ 3 + B ^ 4), hb, by
    calc
      -(B ^ 3 + B ^ 4) * B = B * -(B ^ 3 + B ^ 4) := by noncomm_ring
      _ = 1 := hb⟩

/-- For E73 the polynomial `B⁵ + B + 1 = 0` supplies the missing inverse. -/
theorem ring73 (A B : R)
    (h1 : B ^ 2 * A = 1) (h2 : A + B * A + B ^ 3 = 0) :
    Commute A B ∧ IsUnit A ∧ IsUnit B := by
  have hba : B * A = -1 - B ^ 4 := by
    linear_combination (norm := noncomm_ring) B * h2 - h1
  have ha : A = 1 + B ^ 4 - B ^ 3 := by
    linear_combination (norm := noncomm_ring) h2 - hba
  have hc : Commute A B := by rw [ha]; show _ * B = B * _; noncomm_ring
  have hab : A * B ^ 2 = 1 := by
    calc
      A * B ^ 2 = B ^ 2 * A := by rw [ha]; noncomm_ring
      _ = 1 := h1
  refine ⟨hc, isUnit_iff_exists.mpr ⟨B ^ 2, hab, h1⟩, ?_⟩
  have hb : B * (-1 - B ^ 4) = 1 := by
    calc
      B * (-1 - B ^ 4) = B * (B * A) := by rw [hba]
      _ = 1 := by simpa only [pow_two, mul_assoc] using h1
  exact isUnit_iff_exists.mpr ⟨-1 - B ^ 4, hb, by
    calc
      (-1 - B ^ 4) * B = B * (-1 - B ^ 4) := by noncomm_ring
      _ = 1 := hb⟩

/-- E118 likewise forces commutation; no matrix dimension or finiteness is used. -/
theorem ring118 (A B : R)
    (h1 : B * A ^ 2 = 1) (h2 : A + B * A * B + B ^ 2 = 0) :
    Commute A B ∧ IsUnit A ∧ IsUnit B := by
  have h3 : A ^ 3 + B * A + B = 0 := by
    linear_combination (norm := noncomm_ring) h2 * A ^ 2 - B * A * h1 - B * h1
  have hba : B * A = -A ^ 4 - 1 := by
    linear_combination (norm := noncomm_ring) h3 * A - h1
  have hb : B = A ^ 4 - A ^ 3 + 1 := by
    linear_combination (norm := noncomm_ring) h3 - hba
  have hc : Commute A B := by rw [hb]; show A * _ = _ * A; noncomm_ring
  have hi : A ^ 2 * B = 1 := by
    calc
      A ^ 2 * B = B * A ^ 2 := by rw [hb]; noncomm_ring
      _ = 1 := h1
  refine ⟨hc, isUnit_iff_exists.mpr ⟨B * A, ?_, ?_⟩,
    isUnit_iff_exists.mpr ⟨A ^ 2, h1, hi⟩⟩
  · calc
      A * (B * A) = B * A ^ 2 := by rw [hb]; noncomm_ring
      _ = 1 := h1
  · simpa only [pow_two, mul_assoc] using h1

/-- The sandwich identity alone suffices for E125. -/
theorem ring125 (A B : R) (h : B * A * B = 1) :
    Commute A B ∧ IsUnit A ∧ IsUnit B := by
  have h' : B * (A * B) = 1 := by simpa only [mul_assoc] using h
  have hc : B * A = A * B := left_inv_eq_right_inv h h'
  have ha : A * B ^ 2 = 1 := by
    calc
      A * B ^ 2 = (A * B) * B := by noncomm_ring
      _ = 1 := by rw [← hc]; exact h
  have ha' : B ^ 2 * A = 1 := by
    calc
      B ^ 2 * A = B * (B * A) := by noncomm_ring
      _ = 1 := by rw [hc]; exact h'
  exact ⟨hc.symm, isUnit_iff_exists.mpr ⟨B ^ 2, ha, ha'⟩,
    isUnit_iff_exists_and_exists.mpr ⟨⟨A * B, h'⟩, ⟨B * A, h⟩⟩⟩

/-- The term operation `y * (y * x)` turns the E1692 coefficients into E73
coefficients. Applying `ring73` then recovers the inverse of the original `B`. -/
theorem ring1692 (A B : R)
    (h1 : (A + B * A) * B = 1) (h2 : (A + B * A) * A + B ^ 2 = 0) :
    Commute A B ∧ IsUnit A ∧ IsUnit B := by
  let D := A + B * A
  change D * B = 1 at h1
  change D * A + B ^ 2 = 0 at h2
  have hq1 : D ^ 2 * B ^ 2 = 1 := by
    linear_combination (norm := noncomm_ring) D * h1 * B + h1
  have hq2 : B ^ 2 + D * B ^ 2 + D ^ 3 = 0 := by
    dsimp [D] at *
    linear_combination (norm := noncomm_ring)
      h2 + (A + B * A) * h2 + (A + B * A) * h1 * A
  obtain ⟨_, _, hd⟩ := ring73 (B ^ 2) D hq1 hq2
  obtain ⟨C, _, hcd⟩ := isUnit_iff_exists.mp hd
  have hcb : C = B := left_inv_eq_right_inv hcd h1
  have hbd : B * D = 1 := hcb ▸ hcd
  have hb : IsUnit B := isUnit_iff_exists.mpr ⟨D, hbd, h1⟩
  have ha : A = -B ^ 3 := by
    linear_combination (norm := noncomm_ring) B * h2 - hbd * A
  refine ⟨?_, ha ▸ (hb.pow 3).neg, hb⟩
  rw [ha]
  show -B ^ 3 * B = B * -B ^ 3
  noncomm_ring

end Ring

section Additive
variable {G : Type*} [AddCommGroup G]

def op (A B : AddMonoid.End G) (c x y : G) : G := A x + B y + c

private theorem end_mul_apply (A B : AddMonoid.End G) (x : G) :
    (A * B) x = A (B x) := rfl

private theorem end_add_apply (A B : AddMonoid.End G) (x : G) :
    (A + B) x = A x + B x := rfl

private theorem separate (P Q : AddMonoid.End G) (k : G)
    (h : ∀ x y, x = P x + Q y + k) : P = 1 ∧ Q = 0 := by
  have hk : k = 0 := by simpa only [map_zero, zero_add] using (h 0 0).symm
  constructor
  · apply AddMonoidHom.ext
    intro x
    simpa only [map_zero, hk, add_zero] using (h x 0).symm
  · apply AddMonoidHom.ext
    intro y
    simpa only [map_zero, hk, zero_add, add_zero] using (h 0 y).symm

theorem coefficients63 (A B : AddMonoid.End G) (c : G)
    (h : @Equation63 G ⟨op A B c⟩) :
    B * A + B ^ 2 * A = 1 ∧ A + B ^ 3 = 0 := by
  apply separate _ _ (B (B c) + B c + c)
  intro x y
  calc
    x = op A B c y (op A B c x (op A B c x y)) := h x y
    _ = _ := by
      simp only [op, map_add, pow_succ, pow_zero, one_mul,
        end_mul_apply, end_add_apply]
      abel

theorem coefficients73 (A B : AddMonoid.End G) (c : G)
    (h : @Equation73 G ⟨op A B c⟩) :
    B ^ 2 * A = 1 ∧ A + B * A + B ^ 3 = 0 := by
  apply separate _ _ (B (B c) + B c + c)
  intro x y
  calc
    x = op A B c y (op A B c y (op A B c x y)) := h x y
    _ = _ := by
      simp only [op, map_add, pow_succ, pow_zero, one_mul,
        end_mul_apply, end_add_apply]
      abel

theorem coefficients118 (A B : AddMonoid.End G) (c : G)
    (h : @Equation118 G ⟨op A B c⟩) :
    B * A ^ 2 = 1 ∧ A + B * A * B + B ^ 2 = 0 := by
  apply separate _ _ (B (A c) + B c + c)
  intro x y
  calc
    x = op A B c y (op A B c (op A B c x y) y) := h x y
    _ = _ := by
      simp only [op, map_add, pow_succ, pow_zero, one_mul,
        end_mul_apply, end_add_apply]
      abel

theorem coefficients125 (A B : AddMonoid.End G) (c : G)
    (h : @Equation125 G ⟨op A B c⟩) :
    B * A * B = 1 ∧ A + B * A ^ 2 + B ^ 2 = 0 := by
  apply separate _ _ (B (A c) + B c + c)
  intro x y
  calc
    x = op A B c y (op A B c (op A B c y x) y) := h x y
    _ = _ := by
      simp only [op, map_add, pow_succ, pow_zero, one_mul,
        end_mul_apply, end_add_apply]
      abel

theorem coefficients1692 (A B : AddMonoid.End G) (c : G)
    (h : @Equation1692 G ⟨op A B c⟩) :
    (A + B * A) * B = 1 ∧ (A + B * A) * A + B ^ 2 = 0 := by
  apply separate _ _ (A c + B (A c) + B c + c)
  intro x y
  calc
    x = op A B c (op A B c y x) (op A B c (op A B c y x) y) := h x y
    _ = _ := by
      simp only [op, map_add, pow_succ, pow_zero, one_mul,
        end_mul_apply, end_add_apply]
      abel

/-- This covers every affine model of all five laws, including infinite abelian
groups and arbitrary additive endomorphisms as the starting coefficients. -/
theorem commuting_units (A B : AddMonoid.End G) (c : G)
    (h : @Equation63 G ⟨op A B c⟩ ∨ @Equation73 G ⟨op A B c⟩ ∨
      @Equation118 G ⟨op A B c⟩ ∨ @Equation125 G ⟨op A B c⟩ ∨
      @Equation1692 G ⟨op A B c⟩) : Commute A B ∧ IsUnit A ∧ IsUnit B := by
  rcases h with h | h | h | h | h
  · obtain ⟨h1, h2⟩ := coefficients63 A B c h
    exact ring63 A B h1 h2
  · obtain ⟨h1, h2⟩ := coefficients73 A B c h
    exact ring73 A B h1 h2
  · obtain ⟨h1, h2⟩ := coefficients118 A B c h
    exact ring118 A B h1 h2
  · exact ring125 A B (coefficients125 A B c h).1
  · obtain ⟨h1, h2⟩ := coefficients1692 A B c h
    exact ring1692 A B h1 h2

theorem bijective_of_unit (A : AddMonoid.End G) (h : IsUnit A) :
    Function.Bijective A := by
  obtain ⟨B, hab, hba⟩ := isUnit_iff_exists.mp h
  have hl : Function.LeftInverse B A := fun x => congrArg (fun f : AddMonoid.End G => f x) hba
  have hr : Function.RightInverse B A := fun x => congrArg (fun f : AddMonoid.End G => f x) hab
  exact ⟨hl.injective, hr.surjective⟩

theorem translations_bijective (A B : AddMonoid.End G) (c : G)
    (ha : IsUnit A) (hb : IsUnit B) (y : G) :
    Function.Bijective (op A B c y) ∧ Function.Bijective (fun x => op A B c x y) := by
  obtain ⟨hai, has⟩ := bijective_of_unit A ha
  obtain ⟨hbi, hbs⟩ := bijective_of_unit B hb
  constructor
  · constructor
    · intro x z hxz
      exact hbi (add_left_cancel (add_right_cancel hxz))
    · intro x
      obtain ⟨z, hz⟩ := hbs (x - A y - c)
      refine ⟨z, ?_⟩
      simp only [op, hz]
      abel
  · constructor
    · intro x z hxz
      exact hai (add_right_cancel (add_right_cancel hxz))
    · intro x
      obtain ⟨z, hz⟩ := has (x - B y - c)
      refine ⟨z, ?_⟩
      simp only [op, hz]
      abel

end Additive
end Affine

spectrum_assert equation1692_iff_left_injective complete
spectrum_assert equation125_iff_left_injective complete
spectrum_assert equation222_iff_right_surjective complete
spectrum_assert malcev125_left complete
spectrum_assert malcev125_right complete
spectrum_assert Affine.commuting_units complete
spectrum_assert Affine.translations_bijective complete

end E63Family
