import equational_theories.Spectrum.Equation1483.PermutationCover

/-! An E1483 permutation extension of any central groupoid is itself central.
This is an equational theorem: no finiteness or constant row is needed. -/
namespace Spectrum.E1483.PermutationCover
variable {G K S : Type*} (f : G → G → G) (a b : G → G → K)
  (hc : ∀ x y z, f (f y x) (f x z) = x)
  (ha : ∀ x y z, b (f y x) (f x (f y z)) = a y x)
  (hb : ∀ x y z, a (f y x) (f x (f y z)) = b x (f y z))

include hc ha hb

/-- The E1483 coefficient conditions strengthen to the central ones. -/
theorem central_coefficients (x y z : G) :
    b (f y x) (f x z) = a y x ∧ a (f y x) (f x z) = b x z := by
  have regular (u v w : G) : f (f w (f u v)) v = f u v := by
    have he := hc (f u v) w (f v v)
    rwa [hc v u v] at he
  have step (u v w : G) : a (f v w) u = b (f (f v w) u) (f u w) := by
    have he := ha u (f v w) (f w w)
    rw [hc w v w] at he
    exact he.symm
  have stable (u v w : G) : a (f w (f u v)) v = a u v := by
    rw [step v w (f u v), regular u v w, ha v u v]
  have first (u v w : G) : b (f v u) (f u w) = a v u := by
    have he := hb (f v u) u w
    rw [hc u v w] at he
    exact he.symm.trans (stable v u u)
  have step' (u v w : G) : a u (f v w) = b (f u (f v w)) w := by
    have he := first (f v w) u (f w w)
    rw [hc w v w] at he
    exact he.symm
  refine ⟨first x y z, ?_⟩
  rw [step' (f y x) x z, hc x y z]

/-- Arbitrary coefficient permutations preserve E168 when the base is E168. -/
theorem extension_central (p : K → S ≃ S) (X Y Z : G × S × S) :
    extension f a b p (extension f a b p Y X) (extension f a b p X Z) = X := by
  rcases X with ⟨x, u, v⟩
  have he := central_coefficients f a b hc ha hb x Y.1 Z.1
  simp only [extension, hc, he.1, he.2,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- info: 'Spectrum.E1483.PermutationCover.extension_central' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extension_central
end Spectrum.E1483.PermutationCover
