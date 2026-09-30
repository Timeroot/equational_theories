import equational_theories.Spectrum.Equation907
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Affine E907 models have odd order. The coefficient maps need not be
assumed to commute: their commutation follows from the law. -/
namespace Spectrum.E907.Affine

/-- A noncommutative coefficient calculation, valid over every unital ring. -/

theorem coefficients_commute {R : Type*} [Ring R] (A B C : R)
    (hbc : B * C = 1) (hcb : C * B = 1)
    (h1 : A * B + B * A = C)
    (h2 : A * A + C * A + B * B = 0) : A * B = B * A := by
  have hbcx (x : R) : B * (C * x) = x := by rw [← mul_assoc, hbc, one_mul]
  have hcbx (x : R) : C * (B * x) = x := by rw [← mul_assoc, hcb, one_mul]
  let D := A * B - B * A
  have he : A * C - C * A + C * A * B - A = 0 := by
    linear_combination (norm := noncomm_ring [hbc, hcb, hbcx, hcbx])
      h2 * B - B * h2 - A * h1 + h1 * A
  have hDB : D * B = D := by
    have h := congrArg (fun z => B * z * B) he
    dsimp [D]
    linear_combination (norm := noncomm_ring [hbc, hcb, hbcx, hcbx]) h
  have hsum : D * B + B * D = 0 := by
    dsimp [D]
    linear_combination (norm := noncomm_ring [hbc, hcb, hbcx, hcbx]) h1 * B - B * h1
  have hBD : B * D = -D := by
    linear_combination (norm := noncomm_ring) hsum - hDB
  have hCD : C * D = -D := by
    have h := congrArg (fun z => C * z) hBD
    linear_combination (norm := noncomm_ring [hcb, hcbx]) h
  have hDC : D * C = D := by
    have h := congrArg (fun z => z * C) hDB
    linear_combination (norm := noncomm_ring [hbc]) -h
  have hADDA : A * D + D * A = D := by
    dsimp [D] at hCD ⊢
    linear_combination (norm := noncomm_ring [hbc, hcb, hbcx, hcbx]) h2 * B - B * h2 - hCD
  have hAD : A * D = D * A := by
    linear_combination (norm := noncomm_ring)
      B * hADDA - h1 * D + A * hBD - hCD - hBD * A + hBD
  have htwo : 2 * (A * D) = D := by
    linear_combination (norm := noncomm_ring) hADDA + hAD
  have htwo' : 2 * (D * A) = D := by
    linear_combination (norm := noncomm_ring) htwo - 2 * hAD
  have hAA : 4 * (A * A * D) = D := by
    linear_combination (norm := noncomm_ring) 2 * A * htwo + htwo
  have hCA : 4 * (C * A * D) = -2 * D := by
    linear_combination (norm := noncomm_ring) 2 * C * htwo + 2 * hCD
  have hBB : 4 * (B * B * D) = 4 * D := by
    linear_combination (norm := noncomm_ring) 4 * B * hBD - 4 * hBD
  have hthree : 3 * D = 0 := by
    linear_combination (norm := noncomm_ring) 4 * h2 * D - hAA - hCA - hBB
  have hAA' : 4 * (D * A * A) = D := by
    linear_combination (norm := noncomm_ring) 2 * htwo' * A + htwo'
  have hCA' : 4 * (D * C * A) = 2 * D := by
    linear_combination (norm := noncomm_ring) 4 * hDC * A + 2 * htwo'
  have hBB' : 4 * (D * B * B) = 4 * D := by
    linear_combination (norm := noncomm_ring) 4 * hDB * B + 4 * hDB
  have hseven : 7 * D = 0 := by
    linear_combination (norm := noncomm_ring) 4 * D * h2 - hAA' - hCA' - hBB'
  have hD : D = 0 := by
    linear_combination (norm := noncomm_ring) hseven - 2 * hthree
  exact sub_eq_zero.mp hD


section Additive
variable {G : Type*} [AddCommGroup G]

def op (A B : AddMonoid.End G) (c x y : G) : G := A x + B y + c

/-- Expanding at zero separates the two coefficient identities from the constant. -/
theorem coefficients (A B : AddMonoid.End G) (c : G)
    (h : @Equation907 G ⟨op A B c⟩) :
    B * (A * B + B * A) = 1 ∧ A + B * A * A + B * B * B = 0 := by
  let k := B (A c) + B (B c) + B c + c
  have he (x y : G) : x = B (A (B x) + B (A x)) +
      (A y + B (A (A y)) + B (B (B y))) + k := by
    calc
      x = op A B c y (op A B c (op A B c y x) (op A B c x y)) := h x y
      _ = _ := by simp only [op, map_add]; dsimp [k]; abel
  have hk : k = 0 := by simpa only [map_zero, add_zero, zero_add] using (he 0 0).symm
  constructor
  · apply AddMonoidHom.ext
    intro x
    change B (A (B x) + B (A x)) = x
    simpa only [map_zero, add_zero, hk] using (he x 0).symm
  · apply AddMonoidHom.ext
    intro y
    change A y + B (A (A y)) + B (B (B y)) = 0
    simpa only [map_zero, zero_add, add_zero, hk] using (he 0 y).symm

/-- E907 forces commutation even when the affine coefficients were unrestricted. -/
theorem commute [Finite G] (A B : AddMonoid.End G) (c : G)
    (h : @Equation907 G ⟨op A B c⟩) : A * B = B * A := by
  obtain ⟨h1,h2⟩ := coefficients A B c h
  have hB : Function.Surjective B := by
    intro x
    refine ⟨(A * B + B * A) x, ?_⟩
    exact congrArg (fun f : AddMonoid.End G => f x) h1
  let e : G ≃+ G := AddEquiv.ofBijective B ⟨Finite.injective_iff_surjective.mpr hB,hB⟩
  let C : AddMonoid.End G := e.symm.toAddMonoidHom
  have hbc : B * C = 1 := by apply AddMonoidHom.ext; intro x; exact e.apply_symm_apply x
  have hcb : C * B = 1 := by apply AddMonoidHom.ext; intro x; exact e.symm_apply_apply x
  have hcbx (x : AddMonoid.End G) : C * (B * x) = x := by
    rw [← mul_assoc, hcb, one_mul]
  have h1' : A * B + B * A = C := by
    linear_combination (norm := noncomm_ring [hcbx]) C * h1
  have h2' : A * A + C * A + B * B = 0 := by
    linear_combination (norm := noncomm_ring [hcbx]) C * h2
  exact coefficients_commute A B C hbc hcb h1' h2'

/-- Doubling is injective in the underlying additive group of a finite affine model. -/
theorem eq_zero_of_double [Finite G] (A B : AddMonoid.End G) (c : G)
    (h : @Equation907 G ⟨op A B c⟩) (x : G) (hx : x + x = 0) : x = 0 := by
  have hcomm := commute A B c h
  have h1 := (coefficients A B c h).1
  have hhalf : B * A * B + B * A * B = 1 := by
    linear_combination (norm := noncomm_ring) h1 + B * hcomm
  have he := congrArg (fun f : AddMonoid.End G => f x) hhalf
  change (B * A * B) x + (B * A * B) x = x at he
  rw [← map_add, hx, map_zero] at he
  exact he.symm

/-- Every finite affine E907 magma over an abelian group has odd cardinality. -/
theorem odd_card [Fintype G] (A B : AddMonoid.End G) (c : G)
    (h : @Equation907 G ⟨op A B c⟩) : Odd (Fintype.card G) := by
  by_contra hn
  have hd : 2 ∣ Fintype.card G := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hn)
  obtain ⟨x,hx⟩ := exists_prime_addOrderOf_dvd_card 2 hd
  have hxx : x + x = 0 := by
    simpa only [hx, two_nsmul] using addOrderOf_nsmul_eq_zero x
  have hz := eq_zero_of_double A B c h x hxx
  simp [hz] at hx

end Additive

spectrum_assert coefficients_commute complete
spectrum_assert commute complete
spectrum_assert odd_card complete

end Spectrum.E907.Affine
