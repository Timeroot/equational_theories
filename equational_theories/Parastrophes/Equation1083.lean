import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All

/-! Cancellation in arbitrary E1083 magmas. The original identity makes
`L_y ∘ R_y` invertible even without finiteness; its inverse is `x ↦ x*(y*x)`.
This proves right injectivity, but does not by itself prove either translation
bijective. -/
namespace Parastrophes.Eq1083

variable {G : Type*} [Magma G]

/-- The reverse composite identity follows from two instances of E1083. -/
theorem reverse_identity (h : Equation1083 G) (x y : G) :
    (y ◇ (x ◇ y)) ◇ (y ◇ (y ◇ (x ◇ y))) = x := by
  have hy : x ◇ ((y ◇ (x ◇ y)) ◇ x) = y := (h y x).symm
  simpa only [hy] using (h x (y ◇ (x ◇ y))).symm

/-- Each column is injective, on arbitrary carriers. -/
theorem right_injective (h : Equation1083 G) (y : G) :
    Function.Injective (fun x => x ◇ y) := by
  intro a b hab
  change a ◇ y = b ◇ y at hab
  rw [← reverse_identity h a y, ← reverse_identity h b y, hab]

/-- The two translations together are a permutation even when neither is
known to be a permutation individually. -/
def translationEquiv (h : Equation1083 G) (y : G) : G ≃ G where
  toFun x := y ◇ (x ◇ y)
  invFun x := x ◇ (y ◇ x)
  left_inv x := reverse_identity h x y
  right_inv x := (h x y).symm

theorem left_injective_iff_right_surjective (h : Equation1083 G) (y : G) :
    Function.Injective (fun x => y ◇ x) ↔
      Function.Surjective (fun x => x ◇ y) := by
  constructor
  · intro hi z
    obtain ⟨a, ha⟩ := (translationEquiv h y).surjective (y ◇ z)
    exact ⟨a, hi ha⟩
  · intro hs a b hab
    obtain ⟨a', rfl⟩ := hs a
    obtain ⟨b', rfl⟩ := hs b
    exact congrArg (fun x => x ◇ y) ((translationEquiv h y).injective hab)

/-- For E1083, proving either side bijective would prove the other side too. -/
theorem left_quasigroup_iff_right (h : Equation1083 G) :
    IsSideQuasigroup .left (inferInstance : Magma G) ↔
      IsSideQuasigroup .right (inferInstance : Magma G) := by
  constructor
  · intro hl y
    exact ⟨right_injective h y, (left_injective_iff_right_surjective h y).mp (hl y).1⟩
  · intro hr y
    refine ⟨(left_injective_iff_right_surjective h y).mpr (hr y).2, ?_⟩
    intro x
    exact ⟨(x ◇ (y ◇ x)) ◇ y, (h x y).symm⟩

end Parastrophes.Eq1083
