import equational_theories.Spectrum.Equation667SimpleTwelve
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Restrictions on finite E667 models, including three order-twelve subclasses.
Commutativity makes squaring an endomorphism. At order twelve, simplicity and
an involution parity count rule out that case. A left identity forces constant
squaring, so associative models and models with a left identity cannot have
any nonzero order divisible by three. These arguments use no new SAT checks. -/

namespace Spectrum.E667

variable {A : Type*} [Magma A] [Finite A]

/-- Solve the defining law for the second input of a known product. -/
theorem rotate_product (h : Equation667 A) (x y : A) :
    (x ◇ y) ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ x) = y := by
  apply E667883.left_injective667 h x
  exact (h (x ◇ y) x).symm

/-- Commutativity makes squaring an endomorphism, although this fails for
general E667 magmas. -/
theorem square_hom_of_commutative (h : Equation667 A)
    (hc : ∀ x y : A, x ◇ y = y ◇ x) (x y : A) :
    (x ◇ y) ◇ (x ◇ y) = (x ◇ x) ◇ (y ◇ y) := by
  let z := x ◇ y
  let t := (z ◇ z) ◇ x
  have hzt : z ◇ t = y := rotate_product h x y
  have htz : t ◇ z = y := (hc t z).trans hzt
  have ht : (y ◇ y) ◇ t = x := by
    apply E667883.left_injective667 h y
    have hr := rotate_product h t z
    rw [htz] at hr
    exact hr.trans (hc x y)
  have hr := rotate_product h (y ◇ y) t
  rw [ht] at hr
  apply E667883.left_injective667 h x
  exact ((hc x (z ◇ z)).trans hr.symm)

/-- In a commutative Latin magma of even order, squaring cannot be injective.
Here the inverse-symbol involution is given by the defining E667 term. -/
theorem odd_card_of_commutative_square_injective [Fintype A] [Nonempty A]
    (h : Equation667 A) (hc : ∀ x y : A, x ◇ y = y ◇ x)
    (hs : Function.Injective (fun x : A => x ◇ x)) : Fintype.card A % 2 = 1 := by
  classical
  obtain ⟨a⟩ := ‹Nonempty A›
  let w := a ◇ a
  let d : Function.End A := fun y => w ◇ ((w ◇ w) ◇ y)
  have hd (y : A) : y ◇ d y = w := (h w y).symm
  have hi (y : A) : d (d y) = y := by
    apply E667883.left_injective667 h (d y)
    exact (hd (d y)).trans ((hc (d y) y).trans (hd y)).symm
  have hf : d ^ 2 ^ 1 = 1 := by
    funext y
    exact hi y
  have fixed (y : A) : d y = y ↔ y = a := by
    constructor
    · intro hy
      exact hs (by simpa only [hy] using hd y)
    · intro hy
      rw [hy]
      apply E667883.left_injective667 h a
      exact hd a
  let e : d.fixedPoints ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨a, (fixed a).mpr rfl⟩
    left_inv := fun y => Subtype.ext ((fixed y.val).mp y.property).symm
    right_inv := fun _ => rfl }
  have hp := Equiv.Perm.card_fixedPoints_modEq hf
  simpa only [Nat.ModEq, Fintype.card_congr e, Fintype.card_unit] using hp

/-- Commutative models of order twelve are impossible. Squaring is an
endomorphism, so simplicity makes it either constant or bijective. The first
case is excluded modulo three and the second by the involution parity count. -/
theorem not_commutative_twelve (h : Equation667 A) (hcard : Nat.card A = 12) :
    ¬ ∀ x y : A, x ◇ y = y ◇ x := by
  classical
  intro hc
  letI : Fintype A := Fintype.ofFinite A
  obtain ⟨a⟩ : Nonempty A := Finite.card_pos_iff.mp (by omega)
  let B := {z : A // ∃ x : A, x ◇ x = z}
  letI : Fintype B := Fintype.ofFinite B
  letI : Magma B := ⟨fun b c => ⟨b.val ◇ c.val, by
    obtain ⟨x, hx⟩ := b.property
    obtain ⟨y, hy⟩ := c.property
    exact ⟨x ◇ y, (square_hom_of_commutative h hc x y).trans (by rw [hx, hy])⟩⟩⟩
  let π : A → B := fun x => ⟨x ◇ x, x, rfl⟩
  have hB : Equation667 B := fun x y => Subtype.ext (h x.val y.val)
  have surj : Function.Surjective π := by
    rintro ⟨b, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hom (x y : A) : π (x ◇ y) = π x ◇ π y :=
    Subtype.ext (square_hom_of_commutative h hc x y)
  rcases quotient_card_twelve h hB hcard π surj hom with h1 | h12
  · haveI : Subsingleton B := Fintype.card_le_one_iff_subsingleton.mp
      (by simpa only [← Nat.card_eq_fintype_card] using (show Nat.card B ≤ 1 by omega))
    have hs (x : A) : x ◇ x = a ◇ a := congrArg Subtype.val (Subsingleton.elim (π x) (π a))
    exact ConstantDiagonal.not_constant_of_three_dvd h (a ◇ a)
      (by simpa only [Nat.card_eq_fintype_card] using (show 3 ∣ Nat.card A by omega)) hs
  · have hπ : Function.Injective π :=
      ((Fintype.bijective_iff_surjective_and_card π).mpr
        ⟨surj, by simpa only [← Nat.card_eq_fintype_card] using hcard.trans h12.symm⟩).1
    have hs : Function.Injective (fun x : A => x ◇ x) := fun x y he => hπ (Subtype.ext he)
    haveI : Nonempty A := ⟨a⟩
    have hp := odd_card_of_commutative_square_injective h hc hs
    rw [← Nat.card_eq_fintype_card, hcard] at hp
    contradiction

theorem left_identity_constant (h : Equation667 A) (e : A)
    (he : ∀ x, e ◇ x = x) (x : A) : x ◇ x = e := by
  apply (square_fiber_iff h e (he e) x).mpr
  rw [he, he]

theorem not_left_identity_of_three_dvd [Fintype A] (h : Equation667 A)
    (hd : 3 ∣ Fintype.card A) (e : A) : ¬ ∀ x, e ◇ x = x := by
  intro he
  exact ConstantDiagonal.not_constant_of_three_dvd h e hd
    (left_identity_constant h e he)

/-- Associativity and Latin cancellation supply a left identity without any
prior unital hypothesis. -/
theorem associative_left_identity [Nonempty A] (h : Equation667 A)
    (ha : ∀ x y z : A, (x ◇ y) ◇ z = x ◇ (y ◇ z)) :
    ∃ e : A, ∀ x, e ◇ x = x := by
  obtain ⟨a⟩ := ‹Nonempty A›
  have hs := Finite.injective_iff_surjective.mp (E667883.left_injective667 h a)
  obtain ⟨e, he⟩ := hs a
  refine ⟨e, fun x => E667883.left_injective667 h a ?_⟩
  dsimp only at he ⊢
  rw [← ha, he]

theorem not_associative_of_three_dvd [Fintype A] [Nonempty A]
    (h : Equation667 A) (hd : 3 ∣ Fintype.card A) :
    ¬ ∀ x y z : A, (x ◇ y) ◇ z = x ◇ (y ◇ z) := by
  intro ha
  obtain ⟨e, he⟩ := associative_left_identity h ha
  exact not_left_identity_of_three_dvd h hd e he

spectrum_assert left_identity_constant complete
spectrum_assert rotate_product complete
spectrum_assert square_hom_of_commutative complete
spectrum_assert odd_card_of_commutative_square_injective complete
spectrum_assert not_commutative_twelve complete
spectrum_assert not_left_identity_of_three_dvd complete
spectrum_assert associative_left_identity complete
spectrum_assert not_associative_of_three_dvd complete

end Spectrum.E667
