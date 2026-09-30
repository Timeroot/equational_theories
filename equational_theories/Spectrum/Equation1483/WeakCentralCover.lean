import equational_theories.Spectrum.Equation1483.PermutationCover

/-! E1483 permutation covers preserve E1485, even on infinite carriers.
Thus a cover of an E1485 base cannot supply a counterexample to E1485 itself,
let alone to FO-definability or to its spectrum. -/
namespace Spectrum.E1483.PermutationCover
variable {G K S : Type*} (f : G → G → G) (a b : G → G → K)
  (hf : ∀ x y z, f (f y x) (f x (f y z)) = x)
  (hw : ∀ x y z, f (f y x) (f x (f z y)) = x)
  (ha : ∀ x y z, b (f y x) (f x (f y z)) = a y x)
  (hb : ∀ x y z, a (f y x) (f x (f y z)) = b x (f y z))
include hf hw ha hb

theorem weak_central_coefficients (x y z : G) :
    b (f y x) (f x (f z y)) = a y x ∧
      a (f y x) (f x (f z y)) = b x (f z y) := by
  have stable (u v : G) : a (f v (f u v)) v = a u v := by
    have he := hb (f u v) v (f u v)
    rw [hf v u v, ha v u v] at he
    exact he
  have first : b (f y x) (f x (f z y)) = a y x := by
    have he := hb (f y x) x (f z y)
    rw [hw x y z] at he
    exact he.symm.trans (stable y x)
  have step (u v w : G) : a (f (f v w) u) (f u w) = b u w := by
    have he := hb u (f v w) (f w (f w v))
    rwa [hw w v w] at he
  refine ⟨first, ?_⟩
  calc
    a (f y x) (f x (f z y)) =
        a (f (f x (f z y)) (f (f y x) (f x (f z y)))) (f x (f z y)) :=
      (stable (f y x) (f x (f z y))).symm
    _ = a (f (f x (f z y)) x) (f x (f z y)) := by rw [hw x y z]
    _ = b x (f z y) := step x x (f z y)

/-- The original cover operation already satisfies E1485. -/
theorem extension_weak_central (p : K → S ≃ S) (X Y Z : G × S × S) :
    extension f a b p (extension f a b p Y X)
      (extension f a b p X (extension f a b p Z Y)) = X := by
  rcases X with ⟨x, u, v⟩
  have he := weak_central_coefficients f a b hf hw ha hb x Y.1 Z.1
  simp only [extension, hw, he.1, he.2,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- info: 'Spectrum.E1483.PermutationCover.extension_weak_central' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extension_weak_central
end Spectrum.E1483.PermutationCover
