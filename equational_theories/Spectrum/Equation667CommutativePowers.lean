import equational_theories.Spectrum.Equation667Subclasses

/-! Commutative E667 magmas cannot have order `3 * 2^k`.
Squaring is an endomorphism. Repeatedly pass to its image; injective squaring
forces odd order, while the fiber over an idempotent has constant squaring
and therefore has order prime to three. The only finite exclusion used is
the existing order-three theorem; no new search certificate is needed. -/
namespace Spectrum.E667

universe u

private theorem descent (n : ℕ) :
    ∀ {A : Type u} [Magma A] [Finite A],
      Equation667 A → (∀ x y : A, x ◇ y = y ◇ x) → Nat.card A = n →
      ∀ k, n ∣ 3 * 2 ^ k → (∃ e : A, e ◇ e = e) ∧ ¬ 3 ∣ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ h hc hcard k hd
    classical
    letI : Fintype A := Fintype.ofFinite A
    have hn : 0 < n := Nat.pos_of_dvd_of_pos hd (by positivity)
    haveI : Nonempty A := Finite.card_pos_iff.mp (by omega)
    obtain ⟨a⟩ := ‹Nonempty A›
    by_cases hi : Function.Injective (fun x : A => x ◇ x)
    · have odd := odd_card_of_commutative_square_injective h hc hi
      rw [← Nat.card_eq_fintype_card, hcard] at odd
      have cop : Nat.Coprime n (2 ^ k) :=
        (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr odd)).pow_right k
      have hd3 : n ∣ 3 := cop.dvd_of_dvd_mul_right hd
      have cases : n = 1 ∨ n = 3 := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd3
      rcases cases with h1 | h3
      · haveI : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp
          (by simp only [← Nat.card_eq_fintype_card, hcard, h1, le_refl])
        exact ⟨⟨a, Subsingleton.elim _ _⟩, by rw [h1]; decide⟩
      · exfalso
        apply not_three_667
        exact Law.MagmaLaw.hasModel_of_card (inferInstance : Magma A)
          ((@Law667.models_iff A _).mpr h)
          (by simpa only [Nat.card_eq_fintype_card, h3] using hcard)
    · let B := {z : A // ∃ x : A, x ◇ x = z}
      letI : Fintype B := Fintype.ofFinite B
      letI : Magma B := ⟨fun b c => ⟨b.val ◇ c.val, by
        obtain ⟨x,hx⟩ := b.property
        obtain ⟨y,hy⟩ := c.property
        exact ⟨x ◇ y, (square_hom_of_commutative h hc x y).trans (by rw [hx,hy])⟩⟩⟩
      let π : A → B := fun x => ⟨x ◇ x, x, rfl⟩
      have hB : Equation667 B := fun x y => Subtype.ext (h x.val y.val)
      have commB (x y : B) : x ◇ y = y ◇ x := Subtype.ext (hc x.val y.val)
      have surj : Function.Surjective π := by
        rintro ⟨b,x,hx⟩
        exact ⟨x, Subtype.ext hx⟩
      have hom (x y : A) : π (x ◇ y) = π x ◇ π y :=
        Subtype.ext (square_hom_of_commutative h hc x y)
      have smaller : Nat.card B < n := by
        rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        apply Fintype.card_lt_of_surjective_not_injective π surj
        intro hp
        exact hi (fun x y he => hp (Subtype.ext he))
      have factor := Quotients.card_eq_mul_fiber h hB π hom surj (π a)
      have hdB : Nat.card B ∣ n :=
        ⟨Nat.card {x : A // π x = π a}, by simpa only [hcard] using factor⟩
      obtain ⟨⟨e,he⟩,hthreeB⟩ := ih (Nat.card B) smaller hB commB rfl k (hdB.trans hd)
      have heA : e.val ◇ e.val = e.val := congrArg Subtype.val he
      let C := {x : A // π x = e}
      letI : Fintype C := Fintype.ofFinite C
      letI : Magma C := ⟨fun x y => ⟨x.val ◇ y.val, by
        rw [hom, x.property, y.property, he]⟩⟩
      have hC : Equation667 C := fun x y => Subtype.ext (h x.val y.val)
      let eC : C := ⟨e.val, Subtype.ext heA⟩
      have squareC (x : C) : x ◇ x = eC :=
        Subtype.ext (congrArg (fun z : B => z.val) x.property)
      have hthreeC : ¬ 3 ∣ Nat.card C := by
        intro hdC
        apply ConstantDiagonal.not_constant_of_three_dvd hC eC
          (by simpa only [Nat.card_eq_fintype_card] using hdC) squareC
      refine ⟨⟨e.val,heA⟩, ?_⟩
      intro hn3
      have eqn := Quotients.card_eq_mul_fiber h hB π hom surj e
      rw [hcard] at eqn
      rw [eqn] at hn3
      rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp hn3 with hb | hf
      · exact hthreeB hb
      · exact hthreeC hf

/-- A commutative E667 model whose order divides `3 * 2^k` has an idempotent,
and its order is not divisible by three. -/
theorem commutative_divisor_three_mul_power_two {A : Type*} [Magma A] [Finite A]
    (h : Equation667 A) (hc : ∀ x y : A, x ◇ y = y ◇ x)
    (k : ℕ) (hd : Nat.card A ∣ 3 * 2 ^ k) :
    (∃ e : A, e ◇ e = e) ∧ ¬ 3 ∣ Nat.card A :=
  descent (Nat.card A) h hc rfl k hd

/-- None of the orders `3, 6, 12, 24, 48, 96, ...` admits a commutative E667
model, even though many of these orders admit noncommutative models. -/
theorem not_commutative_three_mul_power_two {A : Type*} [Magma A] [Finite A]
    (h : Equation667 A) (k : ℕ) (hcard : Nat.card A = 3 * 2 ^ k) :
    ¬ ∀ x y : A, x ◇ y = y ◇ x := by
  intro hc
  have hh := (commutative_divisor_three_mul_power_two h hc k (by rw [hcard])).2
  exact hh (by rw [hcard]; exact dvd_mul_right _ _)

spectrum_assert commutative_divisor_three_mul_power_two complete
spectrum_assert not_commutative_three_mul_power_two complete
end Spectrum.E667
