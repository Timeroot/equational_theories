import equational_theories.Definability.CubeTwists
import Mathlib.Data.Finite.Prod

/-! The right cube of an E3545 magma is injective on its own image.
Its canonical partial inverse produces an E3342 companion on any carrier, and
the companion determines the original operation on finite carriers. The explicit
first-order formulas and public definability arrows are in `CubeReverseFO`. -/

namespace CubeTwists

variable {G : Type*} (f : G → G → G)
variable (h : ∀ x y, f x y = f y (rightCube f x))
include h

/-- The right cube has no merging after the first step. -/
theorem rightCube_kernel_stable {x y : G}
    (he : rightCube f (rightCube f x) = rightCube f (rightCube f y)) :
    rightCube f x = rightCube f y := by
  have hq : square f x = square f y := by
    calc
      square f x = square f (rightCube f (rightCube f x)) :=
        ((square_twist f _ h (rightCube f x)).trans (square_twist f _ h x)).symm
      _ = square f (rightCube f (rightCube f y)) := congrArg (square f) he
      _ = square f y :=
        (square_twist f _ h (rightCube f y)).trans (square_twist f _ h y)
  calc
    rightCube f x = f (rightCube f (square f x)) (rightCube f x) :=
      (simultaneous f _ h (square f x) x).symm
    _ = f (rightCube f (rightCube f (square f x))) (rightCube f (rightCube f x)) :=
      (simultaneous f _ h _ _).symm
    _ = f (rightCube f (rightCube f (square f y))) (rightCube f (rightCube f y)) := by
      rw [hq, he]
    _ = f (rightCube f (square f y)) (rightCube f y) := simultaneous f _ h _ _
    _ = rightCube f y := simultaneous f _ h (square f y) y

/-- On its image, the right cube is injective, without any finiteness assumption. -/
theorem rightCube_injective_image :
    Set.InjOn (rightCube f) (Set.range (rightCube f)) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ he
  exact rightCube_kernel_stable f h he

/-- The right cube restricts to a permutation of its image on a finite carrier. -/
theorem rightCube_bijective_image [Finite G] :
    Function.Bijective (fun x : Set.range (rightCube f) =>
      (⟨rightCube f x, ⟨x, rfl⟩⟩ : Set.range (rightCube f))) := by
  apply (Finite.injective_iff_bijective).mp
  intro x y he
  apply Subtype.ext
  exact rightCube_injective_image f h x.property y.property (congrArg Subtype.val he)

end CubeTwists

namespace CubeReverse

variable {G : Type*}

/-- Invert `w` on the image of `w²`; keep other points unchanged. Kernel
stability makes the chosen predecessor unique as an element of `range w`. -/
noncomputable def partialInverse (w : G → G) (z : G) : G := by
  classical
  exact if he : ∃ a, w (w a) = z then w he.choose else z

variable (w : G → G) (hs : ∀ {a b}, w (w a) = w (w b) → w a = w b)
include hs

theorem partialInverse_twice (x : G) : partialInverse w (w (w x)) = w x := by
  classical
  rw [partialInverse, dif_pos ⟨x, rfl⟩]
  exact hs (Exists.choose_spec (show ∃ a, w (w a) = w (w x) from ⟨x, rfl⟩))

theorem partialInverse_graph (z v : G) :
    partialInverse w z = v ↔
      ((∃ a, w a = v) ∧ w v = z) ∨ ((¬ ∃ a, w (w a) = z) ∧ v = z) := by
  classical
  by_cases he : ∃ a, w (w a) = z
  · obtain ⟨a, rfl⟩ := he
    rw [partialInverse_twice w hs]
    constructor
    · rintro rfl
      exact Or.inl ⟨⟨a, rfl⟩, rfl⟩
    · rintro (⟨⟨b, rfl⟩, hb⟩ | ⟨hn, _⟩)
      · exact (hs hb).symm
      · exact (hn ⟨a, rfl⟩).elim
  · rw [partialInverse, dif_neg he]
    constructor
    · intro hv
      exact Or.inr ⟨he, hv.symm⟩
    · rintro (⟨⟨a, rfl⟩, ha⟩ | ⟨_, hv⟩)
      · exact (he ⟨a, ha⟩).elim
      · exact hv.symm

omit hs in
/-- Forward shift on the image, with the identity off the image. -/
noncomputable def forwardInverse (w : G → G) (z : G) : G := by
  classical
  exact if ∃ a, w a = z then w z else z

theorem forwardInverse_partialInverse
    (hr : ∀ z, (∃ a, w a = z) → ∃ a, w (w a) = z) (z : G) :
    forwardInverse w (partialInverse w z) = z := by
  classical
  by_cases he : ∃ a, w (w a) = z
  · obtain ⟨a, rfl⟩ := he
    rw [partialInverse_twice w hs, forwardInverse, if_pos ⟨a, rfl⟩]
  · have hn : ¬ ∃ a, w a = z := fun hx => he (hr z hx)
    rw [partialInverse, dif_neg he, forwardInverse, if_neg hn]

omit hs

open CubeTwists

variable (f : G → G → G)

/-- The conditional reverse-cube construction. -/
noncomputable def companion (x y : G) : G := by
  classical
  exact if square f x = square f y then f x y
    else partialInverse (rightCube f) (f x y)

@[simp] theorem companion_square (x : G) : square (companion f) x = square f x := by
  classical
  simp [square, companion]

variable (h : ∀ x y, f x y = f y (rightCube f x))
include h

/-- Over a fixed square, the first two right cubes coincide. -/
theorem rightCube_twice_eq_of_square_fixed (x : G)
    (hq : square f x = square f (square f x)) :
    rightCube f (rightCube f x) = rightCube f x := by
  have ht : rightCube f (square f x) = square f x := by
    unfold rightCube
    rw [← hq]
    exact hq.symm
  calc
    rightCube f (rightCube f x) = f (square f x) (rightCube f x) := by
      change f (square f (rightCube f x)) (rightCube f x) = _
      rw [square_twist f (rightCube f) h x]
    _ = f (rightCube f (square f x)) (rightCube f x) := by rw [ht]
    _ = rightCube f x := simultaneous f (rightCube f) h (square f x) x

/-- The new left cube is exactly the original right cube. -/
theorem companion_leftCube (x : G) : leftCube (companion f) x = rightCube f x := by
  classical
  change companion f x (square (companion f) x) = _
  rw [companion_square, companion]
  split_ifs with hq
  · exact (leftCube_eq_rightCube_squared f h x).trans
      (rightCube_twice_eq_of_square_fixed f h x hq)
  · change partialInverse (rightCube f) (leftCube f x) = _
    rw [leftCube_eq_rightCube_squared f h x]
    exact partialInverse_twice _ (rightCube_kernel_stable f h) x

/-- This construction satisfies E3342 on arbitrary carriers. -/
theorem companion_law (x y : G) :
    companion f x y = companion f y (leftCube (companion f) x) := by
  classical
  rw [companion_leftCube f h x]
  unfold companion
  rw [square_twist f (rightCube f) h x, h x y]
  by_cases he : square f x = square f y
  · rw [if_pos he, if_pos he.symm]
  · rw [if_neg he, if_neg (Ne.symm he)]

open scoped Classical in
/-- The original product can be read back from the companion on finite carriers. -/
theorem recover [Finite G] (x y : G) :
    (if square (companion f) x = square (companion f) y then companion f x y
      else forwardInverse (leftCube (companion f)) (companion f x y)) = f x y := by
  classical
  have hr : ∀ z, (∃ a, rightCube f a = z) →
      ∃ a, rightCube f (rightCube f a) = z := by
    intro z hz
    obtain ⟨a, ha⟩ := (rightCube_bijective_image f h).surjective ⟨z, hz⟩
    obtain ⟨b, hb⟩ := a.property
    exact ⟨b, by simpa only [← hb] using congrArg Subtype.val ha⟩
  simp only [companion_square]
  by_cases he : square f x = square f y
  · rw [if_pos he, companion, if_pos he]
  · rw [if_neg he, companion, if_neg he]
    have hc : leftCube (companion f) = rightCube f := funext (companion_leftCube f h)
    rw [hc]
    exact forwardInverse_partialInverse _ (rightCube_kernel_stable f h) hr _

end CubeReverse
