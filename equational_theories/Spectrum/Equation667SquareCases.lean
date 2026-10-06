import equational_theories.Spectrum.Equation667Division
import equational_theories.Spectrum.Equation667AutomorphismTwist
import equational_theories.Spectrum.Equation667IdempotentTwelve.Certificate

/-! A complete split for a noninjective square map. Besides a collision above
an idempotent, only two patterns on three or four distinct points are needed.
This reduces the order-twelve search to bijective squaring and three collision
cases; it is not by itself a nonexistence result. -/
namespace Spectrum.E667
variable {Q : Type*} [Magma Q] [Finite Q]

omit [Finite Q] in
theorem square_cases :
    Function.Injective (fun x : Q => x ◇ x) ∨
    (∃ e x : Q, x ≠ e ∧ e ◇ e = e ∧ x ◇ x = e) ∨
    (∃ a b c : Q, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ◇ a = c ∧ b ◇ b = c ∧ c ◇ c = a) ∨
    (∃ a b c d : Q, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      a ◇ a = c ∧ b ◇ b = c ∧ c ◇ c = d) := by
  classical
  by_cases hi : Function.Injective (fun x : Q => x ◇ x)
  · exact Or.inl hi
  right
  obtain ⟨a,b,he,hab⟩ : ∃ a b : Q, a ◇ a = b ◇ b ∧ a ≠ b := by
    by_contra hn
    apply hi
    intro a b he
    by_contra hab
    exact hn ⟨a,b,he,hab⟩
  let c := a ◇ a
  have ha : a ◇ a = c := rfl
  have hb : b ◇ b = c := he.symm
  by_cases hac : a = c
  · left
    exact ⟨a,b,hab.symm,ha.trans hac.symm,hb.trans hac.symm⟩
  by_cases hbc : b = c
  · left
    exact ⟨b,a,hab,hb.trans hbc.symm,ha.trans hbc.symm⟩
  by_cases hc : c ◇ c = c
  · exact Or.inl ⟨c,a,hac,hc,ha⟩
  right
  by_cases hca : c ◇ c = a
  · exact Or.inl ⟨a,b,c,hab,hac,hbc,ha,hb,hca⟩
  by_cases hcb : c ◇ c = b
  · exact Or.inl ⟨b,a,c,hab.symm,hbc,hac,hb,ha,hcb⟩
  exact Or.inr ⟨a,b,c,c ◇ c,hab,hac,Ne.symm hca,hbc,Ne.symm hcb,Ne.symm hc,ha,hb,rfl⟩

/-- With injective squaring, a left translation cannot place its own index
in a genuine two-cycle. -/
theorem two_cycle_idempotent_of_square_injective (h : Equation667 Q)
    (hi : Function.Injective (fun x : Q => x ◇ x)) (x : Q)
    (hx : x ◇ (x ◇ x) = x) : x ◇ x = x :=
  hi (two_cycle_square_idempotent h x hx)

/-- At order twelve an involutive square map must fail to preserve a product:
otherwise removing the square-map twist gives an excluded idempotent model. -/
theorem involutive_square_not_multiplicative_twelve (h : Equation667 Q)
    (hc : Nat.card Q = 12) (hi : Function.Involutive (fun x : Q => x ◇ x)) :
    ∃ x y : Q, (x ◇ y) ◇ (x ◇ y) ≠ (x ◇ x) ◇ (y ◇ y) := by
  classical
  by_contra hn
  have hm : ∀ x y : Q, (x ◇ y) ◇ (x ◇ y) = (x ◇ x) ◇ (y ◇ y) := by
    intro x y
    by_contra he
    exact hn ⟨x,y,he⟩
  let J : Q → Q := fun x => x ◇ x
  have ht := AutomorphismTwist.law J hi hm h
  have hd := (AutomorphismTwist.untwist J hi hm h (fun _ => rfl)).2
  letI : Magma Q := ⟨AutomorphismTwist.op J⟩
  exact not_idempotent_twelve ht hc hd

spectrum_assert square_cases complete
spectrum_assert two_cycle_idempotent_of_square_injective complete
spectrum_assert involutive_square_not_multiplicative_twelve complete
end Spectrum.E667
