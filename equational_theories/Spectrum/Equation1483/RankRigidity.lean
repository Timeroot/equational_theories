import equational_theories.Definability.Central1483Translations
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! An E1483 magma with uniform translation rank r and order r² is central.
Every product is the middle point of a two-step path in its row-image graph;
counting paths makes that middle point unique. -/
namespace Spectrum.E1483.RankRigidity

variable {G : Type*} [Magma G]

abbrev Row (a : G) := {u : G // ∃ z, a ◇ z = u}

/-- A product is followed by its right argument in the row-image graph. -/
theorem right_argument_in_row (h : Equation1483 G) (a x : G) :
    ∃ z, (a ◇ x) ◇ z = x :=
  ⟨x ◇ (a ◇ a), (h x a a).symm⟩

/-- The two-step paths starting at a, including their intermediate vertex. -/
abbrev TwoStep (a : G) := (b : Row a) × Row b.val

/-- If no source has more two-step paths than targets, all intermediates are unique. -/
theorem central_of_two_step_bound [Finite G] (h : Equation1483 G)
    (hcard : ∀ a : G, Nat.card (TwoStep a) ≤ Nat.card G) : Equation168 G := by
  classical
  letI := Fintype.ofFinite G
  letI (a : G) : Fintype (Row a) := Fintype.ofFinite (Row a)
  let lift (a x : G) : TwoStep a :=
    ⟨⟨a ◇ x, x, rfl⟩, ⟨x, right_argument_in_row h a x⟩⟩
  have hinj (a : G) : Function.Injective (lift a) := by
    intro x y he
    exact congrArg (fun p : TwoStep a => p.2.val) he
  have hsurj (a : G) : Function.Surjective (lift a) :=
    ((hinj a).bijective_of_nat_card_le (hcard a)).2
  have middle (a b c : G) (hb : ∃ z, a ◇ z = b) (hc : ∃ z, b ◇ z = c) :
      a ◇ c = b := by
    obtain ⟨x, hx⟩ := hsurj a ⟨⟨b, hb⟩, ⟨c, hc⟩⟩
    have hxb : a ◇ x = b := congrArg (fun p : TwoStep a => p.1.val) hx
    have hxc : x = c := congrArg (fun p : TwoStep a => p.2.val) hx
    exact hxc ▸ hxb
  intro x y z
  exact (middle (y ◇ x) x (x ◇ z) (right_argument_in_row h y x) ⟨z, rfl⟩).symm

/-- Uniform rank attaining the two-step counting bound forces the central law. -/
theorem central_of_uniform_square [Finite G] (h : Equation1483 G) (r : ℕ)
    (hr : ∀ a : G, Nat.card (Row a) = r) (hn : Nat.card G = r ^ 2) :
    Equation168 G := by
  classical
  letI := Fintype.ofFinite G
  letI (a : G) : Fintype (Row a) := Fintype.ofFinite (Row a)
  apply central_of_two_step_bound h
  intro a
  have hc : Nat.card (TwoStep a) = Nat.card G := by
    rw [Nat.card_sigma]
    simp only [hr, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card, hr, hn, pow_two]
  exact hc.le

/-- info: 'Spectrum.E1483.RankRigidity.central_of_uniform_square' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms central_of_uniform_square

end Spectrum.E1483.RankRigidity
