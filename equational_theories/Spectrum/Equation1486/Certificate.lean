import equational_theories.Spectrum.Basic
import equational_theories.Equations.All

/-! A small certificate for E1486: factor multiplication by squares through
an index type, then check one return identity for each index. -/
namespace Spectrum.E1486

theorem law_of_factor {G I : Type*} (f : G → G → G)
    (right : G → I → G) (coord : G → I)
    (hinner : ∀ x z, f x (f z z) = right x (coord z))
    (houter : ∀ x y i, f (f y x) (right x i) = x) :
    @Equation1486 G ⟨f⟩ := by
  intro x y z
  change x = f (f y x) (f x (f z z))
  rw [hinner, houter]

end Spectrum.E1486
