import equational_theories.Spectrum.SmallOrders.Chain

/-! Commutative E1110 operations are automatically idempotent, even on an
infinite carrier. Thus commutative searches do not reach an additional family
beyond idempotent searches. The proof uses only two overlapping instances of
the original identity; cancellation and finiteness are unnecessary. -/

namespace Spectrum.E1110

variable {A : Type*} [Magma A]

theorem idempotent_of_commutative (h : Equation1110 A)
    (hc : ∀ x y : A, x ◇ y = y ◇ x) : ∀ x : A, x ◇ x = x := by
  have cube (x y : A) : y ◇ (y ◇ (y ◇ (x ◇ x))) = x := by
    rw [← hc (y ◇ (x ◇ x)) y]
    exact (h x y).symm
  have absorb (x : A) : x ◇ (x ◇ x) = x ◇ x := by
    have hh := cube (x ◇ x) (x ◇ x)
    rw [cube x (x ◇ x)] at hh
    exact (hc x (x ◇ x)).trans hh
  intro x
  simpa only [absorb] using cube x x

/-- In the commutative case each left translation has cube equal to identity. -/
theorem left_cube_of_commutative (h : Equation1110 A)
    (hc : ∀ x y : A, x ◇ y = y ◇ x) (x y : A) :
    y ◇ (y ◇ (y ◇ x)) = x := by
  have hi := idempotent_of_commutative h hc
  have hh := (h x y).symm
  rw [hi x, hc (y ◇ x) y] at hh
  exact hh

end Spectrum.E1110
