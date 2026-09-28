import equational_theories.Spectrum.Equation1483.ConstantSpectrum
import equational_theories.Definability.FiniteBridge

/-! The cubic untwist gives a parameter-free FO definition on every finite
E1483 magma with a constant row. The constant used by the construction is
fixed by every automorphism, so it is not an externally named parameter. -/

namespace Spectrum.E1483.Constant

variable {G : Type} [M : Magma G]

theorem automorphism_fixes_one (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) (σ : G → G)
    (hsurj : Function.Surjective σ) (hhom : ∀ x y, σ (x ◇ y) = σ x ◇ σ y) :
    σ one = one := by
  have hc : ∀ t, σ zero ◇ t = σ one := by
    intro t
    obtain ⟨u, rfl⟩ := hsurj t
    rw [← hhom, hzero]
  have hz := constant_row_unique h zero one hzero (σ zero) (σ one) hc
  calc
    σ one = σ (zero ◇ zero) := congrArg σ (hzero zero).symm
    _ = σ zero ◇ σ zero := hhom zero zero
    _ = one := by rw [hz, hzero]

/-- A positive result for the entire constant-row subclass, rather than
just a fixed finite example. It does not assert the general E1483 transfer. -/
theorem untwist_definable [Finite G] (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) :
    Law.MagmaLaw.DefinableOnMagma Law1485 M := by
  let N : Magma G := ⟨untwist one⟩
  letI : Magma G := M
  have hn : @Equation1485 G N := by
    intro x y z
    exact (untwist_eqn h zero one hzero x y z).symm
  refine ⟨N, (@Law1485.models_iff G N).mpr hn, ?_⟩
  apply Magma.definable_of_aut_invariant M N.Graph
  intro σ hbij hhom v hv
  have hone := automorphism_fixes_one h zero one hzero σ hbij.2 hhom
  have ht (x : G) : σ (twist one x) = twist one (σ x) := by
    dsimp [twist]
    rw [hhom, hhom, hone]
  have hu (x y : G) : σ (untwist one x y) = untwist one (σ x) (σ y) := by
    dsimp only [untwist]
    rw [hhom, ht, ht, ht]
  change untwist one (σ (v (some 0))) (σ (v (some 1))) = σ (v none)
  rw [← hu]
  exact congrArg σ hv

/-- info: 'Spectrum.E1483.Constant.untwist_definable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms untwist_definable

end Spectrum.E1483.Constant
