import equational_theories.Definability.FiniteSymmetry

/-! Cache the action of permutation words while preserving the orbit-chart operation. -/

namespace Magma.FiniteSymmetry

variable {n g k : ℕ}

def wordImageData (generators : Fin g → Equiv.Perm (Fin n))
    (words : Fin k → List (Fin g)) : Array (Array (Fin n)) :=
  Array.ofFn fun i => Array.ofFn (wordPerm generators (words i))

def cachedWord [NeZero n] (generators : Fin g → Equiv.Perm (Fin n))
    (words : Fin k → List (Fin g)) (i : Fin k) (x : Fin n) : Fin n :=
  ((wordImageData generators words).getD i.val #[]).getD x.val 0

theorem cachedWord_eq [NeZero n] (generators : Fin g → Equiv.Perm (Fin n))
    (words : Fin k → List (Fin g)) (i : Fin k) (x : Fin n) :
    cachedWord generators words i x = wordPerm generators (words i) x := by
  simp [cachedWord, wordImageData, Array.getD]

theorem family_eq_of_images {m : ℕ}
    (generators : Fin g → Equiv.Perm (Fin n)) (words : Fin k → List (Fin g))
    (tr : Fin n → Fin n → Fin m × Fin k) (sizes : Fin m → ℕ)
    (values : (i : Fin m) → Fin (sizes i) → Fin n)
    (image : Fin k → Fin n → Fin n)
    (himage : ∀ i x, image i x = wordPerm generators (words i) x)
    (p : (i : Fin m) → Fin (sizes i)) :
    (⟨fun x y => image (tr x y).2 (values (tr x y).1 (p (tr x y).1))⟩ : Magma (Fin n)) =
      family generators words tr sizes values p := by
  change Magma.mk _ = Magma.mk _
  apply congrArg Magma.mk
  funext x y
  exact himage _ _

/-- info: 'Magma.FiniteSymmetry.cachedWord_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cachedWord_eq

/-- info: 'Magma.FiniteSymmetry.family_eq_of_images' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms family_eq_of_images

end Magma.FiniteSymmetry
