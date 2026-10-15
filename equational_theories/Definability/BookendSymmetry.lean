import equational_theories.Spectrum.BookendCardinality

/-! Every involutive automorphism of a bookend magma has a canonical square
root as a permutation of its carrier. This constrains prospective finite
automorphism obstructions without asserting any new definability arrow. -/
namespace Magma.BookendSymmetry
variable {G : Type*} [Magma G] (h : Equation167 G)

/-- The root is `x ↦ x ◇ σ x`; its inverse is `x ↦ σ x ◇ x`. -/
def root (σ : Equiv.Perm G) (hi : Function.Involutive σ)
    (ha : ∀ x y, σ (x ◇ y) = σ x ◇ σ y) : Equiv.Perm G where
  toFun x := x ◇ σ x
  invFun x := σ x ◇ x
  left_inv x := by
    change σ (x ◇ σ x) ◇ (x ◇ σ x) = x
    rw [ha,hi]
    exact (h x (σ x)).symm
  right_inv x := by
    change (σ x ◇ x) ◇ σ (σ x ◇ x) = x
    rw [ha,hi]
    exact (h x (σ x)).symm

theorem root_twice (σ : Equiv.Perm G) (hi : Function.Involutive σ)
    (ha : ∀ x y, σ (x ◇ y) = σ x ◇ σ y) (x : G) :
    root h σ hi ha (root h σ hi ha x) = σ x := by
  change (x ◇ σ x) ◇ σ (x ◇ σ x) = σ x
  rw [ha,hi]
  exact (h (σ x) x).symm

theorem root_sq (σ : Equiv.Perm G) (hi : Function.Involutive σ)
    (ha : ∀ x y, σ (x ◇ y) = σ x ◇ σ y) :
    root h σ hi ha * root h σ hi ha = σ := by
  ext x
  exact root_twice h σ hi ha x

include h in
/-- In particular an involutive automorphism can never be an odd permutation. -/
theorem involutive_auto_even [Fintype G] [DecidableEq G]
    (σ : Equiv.Perm G) (hi : Function.Involutive σ)
    (ha : ∀ x y, σ (x ◇ y) = σ x ◇ σ y) : Equiv.Perm.sign σ = 1 := by
  rw [← root_sq h σ hi ha,Equiv.Perm.sign_mul]
  exact Int.units_mul_self _

/-- The construction is invariant under every source automorphism commuting
with the original involution, even when the carrier is infinite. -/
theorem root_commutes (σ : Equiv.Perm G) (hi : Function.Involutive σ)
    (ha : ∀ x y, σ (x ◇ y) = σ x ◇ σ y) (τ : Equiv.Perm G)
    (ht : ∀ x y, τ (x ◇ y) = τ x ◇ τ y) (hc : Function.Commute τ σ) :
    Function.Commute τ (root h σ hi ha) := by
  intro x
  change τ (x ◇ σ x) = τ x ◇ σ (τ x)
  rw [ht,hc x]

end Magma.BookendSymmetry
