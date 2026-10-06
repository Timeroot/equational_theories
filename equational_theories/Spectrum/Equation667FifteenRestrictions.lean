import equational_theories.Spectrum.Equation667SimpleFifteen
import equational_theories.Spectrum.Equation667Subclasses

namespace Spectrum.E667
variable {A : Type*} [Magma A] [Finite A]

/-- Simplicity forces the commutative squaring endomorphism to be injective:
its constant alternative is excluded at every order divisible by three. -/
theorem square_injective_commutative_fifteen (h : Equation667 A)
    (hc : ∀ x y : A, x ◇ y = y ◇ x) (hcard : Nat.card A = 15) :
    Function.Injective (fun x : A => x ◇ x) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  obtain ⟨a⟩ : Nonempty A := Finite.card_pos_iff.mp (by omega)
  let B := {z : A // ∃ x : A, x ◇ x = z}
  letI : Fintype B := Fintype.ofFinite B
  letI : Magma B := ⟨fun b c => ⟨b.val ◇ c.val, by
    obtain ⟨x,hx⟩ := b.property
    obtain ⟨y,hy⟩ := c.property
    exact ⟨x ◇ y, (square_hom_of_commutative h hc x y).trans (by rw [hx,hy])⟩⟩⟩
  let π : A → B := fun x => ⟨x ◇ x, x, rfl⟩
  have hB : Equation667 B := fun x y => Subtype.ext (h x.val y.val)
  have surj : Function.Surjective π := by
    rintro ⟨b,x,hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hom (x y : A) : π (x ◇ y) = π x ◇ π y :=
    Subtype.ext (square_hom_of_commutative h hc x y)
  rcases quotient_card_fifteen h hB hcard π surj hom with h1 | h15
  · haveI : Subsingleton B := Fintype.card_le_one_iff_subsingleton.mp
      (by simpa only [← Nat.card_eq_fintype_card] using (show Nat.card B ≤ 1 by omega))
    have hs (x : A) : x ◇ x = a ◇ a := congrArg Subtype.val (Subsingleton.elim (π x) (π a))
    exact False.elim (ConstantDiagonal.not_constant_of_three_dvd h (a ◇ a)
      (by simpa only [Nat.card_eq_fintype_card] using (show 3 ∣ Nat.card A by omega)) hs)
  · have hπ : Function.Injective π :=
      ((Fintype.bijective_iff_surjective_and_card π).mpr
        ⟨surj, by simpa only [← Nat.card_eq_fintype_card] using hcard.trans h15.symm⟩).1
    exact fun x y he => hπ (Subtype.ext he)

/-- At order fifteen a commutative model cannot contain any idempotent.
The square of its left translation would be an involution with seven
transpositions, but a square permutation always has positive sign. -/
theorem no_idempotent_commutative_fifteen (h : Equation667 A)
    (hc : ∀ x y : A, x ◇ y = y ◇ x) (hcard : Nat.card A = 15) (e : A) : e ◇ e ≠ e := by
  classical
  intro he
  letI : Fintype A := Fintype.ofFinite A
  have hs := square_injective_commutative_fifteen h hc hcard
  let L : Equiv.Perm A := Equiv.ofBijective (fun y => e ◇ y)
    ⟨E667883.left_injective667 h e,
      Finite.injective_iff_surjective.mp (E667883.left_injective667 h e)⟩
  let σ := L ^ 2
  have sq (y : A) : σ y = e ◇ (e ◇ y) := rfl
  have hr (y : A) : y ◇ σ y = e := by
    simpa only [sq, he] using (h e y).symm
  have invol : σ ^ 2 = 1 := by
    ext y
    change σ (σ y) = y
    apply E667883.left_injective667 h (σ y)
    exact (hr (σ y)).trans ((hc (σ y) y).trans (hr y)).symm
  have fixed (y : A) : σ y = y ↔ y = e := by
    constructor
    · intro hy
      apply hs
      have ht : y ◇ y = e := by simpa only [hy] using hr y
      exact ht.trans he.symm
    · intro hy
      rw [hy, sq, he, he]
  let ef : Function.fixedPoints σ ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨e, (fixed e).mpr rfl⟩
    left_inv := fun y => Subtype.ext ((fixed y.val).mp y.property).symm
    right_inv := fun _ => rfl }
  have positive : Equiv.Perm.sign σ = 1 := by
    change Equiv.Perm.sign (L ^ 2) = 1
    rw [map_pow]
    exact Int.units_sq _
  have sign := Equiv.Perm.sign_of_pow_two_eq_one invol
  rw [positive, Fintype.card_congr ef, Fintype.card_unit,
    ← Nat.card_eq_fintype_card, hcard] at sign
  norm_num at sign

spectrum_assert square_injective_commutative_fifteen complete
spectrum_assert no_idempotent_commutative_fifteen complete
end Spectrum.E667
