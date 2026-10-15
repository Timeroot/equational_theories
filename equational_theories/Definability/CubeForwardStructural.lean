import equational_theories.Definability.CubeConditional
import equational_theories.Definability.CubeReverseFO

/-!
# A reversible finite E3342 → E3545 interpretation

Extend the left cube to a permutation by using it on its image and the identity
elsewhere. Apply this permutation to a product precisely when the two input
squares differ. The right cube of the resulting operation is the original left
cube, so its canonical inverse recovers every original product.

This is the inverse of `CubeReverse.companionMagma`, not the potentially lossy
quantifier-free construction in `CubeConditional`.
-/

open Law Law.MagmaLaw CubeTwists CubeReverse

namespace CubeForwardStructural

variable {G : Type} (M : Magma G) (h : @Equation3342 G M)
include h

/-- Like the right cube in E3545, the left cube has stable kernel in E3342. -/
theorem leftCube_kernel_stable {x y : G}
    (he : leftCube M.op (leftCube M.op x) = leftCube M.op (leftCube M.op y)) :
    leftCube M.op x = leftCube M.op y := by
  have hq : square M.op x = square M.op y := by
    calc
      square M.op x = square M.op (leftCube M.op (leftCube M.op x)) :=
        ((square_twist M.op (leftCube M.op) h (leftCube M.op x)).trans
          (square_twist M.op (leftCube M.op) h x)).symm
      _ = square M.op (leftCube M.op (leftCube M.op y)) := congrArg (square M.op) he
      _ = square M.op y := (square_twist M.op (leftCube M.op) h _).trans (square_twist M.op (leftCube M.op) h y)
  calc
    leftCube M.op x = M.op (leftCube M.op x) (leftCube M.op (square M.op x)) :=
      (simultaneous M.op (leftCube M.op) h x (square M.op x)).symm
    _ = M.op (leftCube M.op (leftCube M.op x))
        (leftCube M.op (leftCube M.op (square M.op x))) :=
      (simultaneous M.op (leftCube M.op) h _ _).symm
    _ = M.op (leftCube M.op (leftCube M.op y))
        (leftCube M.op (leftCube M.op (square M.op y))) := by rw [hq, he]
    _ = M.op (leftCube M.op y) (leftCube M.op (square M.op y)) := simultaneous M.op (leftCube M.op) h _ _
    _ = leftCube M.op y := simultaneous M.op (leftCube M.op) h y (square M.op y)

section finite
variable [Finite G]

theorem leftCube_bijective_image :
    Function.Bijective (fun x : Set.range (leftCube M.op) =>
      (⟨leftCube M.op x, ⟨x, rfl⟩⟩ : Set.range (leftCube M.op))) := by
  apply (Finite.injective_iff_bijective).mp
  rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ he
  exact Subtype.ext (leftCube_kernel_stable M h (congrArg Subtype.val he))

/-- Every right cube is in the stable image of the left cube. -/
theorem rightCube_mem_image (x : G) : ∃ a, leftCube M.op a = rightCube M.op x := by
  obtain ⟨a, ha⟩ := (leftCube_bijective_image M h).surjective ⟨leftCube M.op x, ⟨x, rfl⟩⟩
  have he : leftCube M.op a = leftCube M.op x := congrArg Subtype.val ha
  have hq : square M.op a = square M.op x := by
    rw [← square_twist M.op (leftCube M.op) h (a : G), he, square_twist M.op (leftCube M.op) h]
  have ht : rightCube M.op a = rightCube M.op x := by
    change M.op (square M.op a) a = M.op (square M.op x) x
    rw [← simultaneous M.op (leftCube M.op) h (square M.op a) a, hq, he,
      simultaneous M.op (leftCube M.op) h]
  obtain ⟨b, hb⟩ := a.property
  refine ⟨b, ?_⟩
  calc
    leftCube M.op b = rightCube M.op (leftCube M.op b) := (rightCube_leftCube M.op h b).symm
    _ = rightCube M.op a := congrArg (rightCube M.op) hb
    _ = rightCube M.op x := ht

omit h [Finite G] in
open scoped Classical in
theorem forward_apply (x y : G) :
    (recoveryMagma M).op x y =
      if square M.op x = square M.op y then M.op x y
      else forwardInverse (leftCube M.op) (M.op x y) := rfl

omit h [Finite G] in
theorem forward_square (x : G) :
    square (recoveryMagma M).op x = square M.op x := by
  classical
  change (recoveryMagma M).op x x = M.op x x
  rw [forward_apply, if_pos rfl]

theorem forward_rightCube (x : G) :
    rightCube (recoveryMagma M).op x = leftCube M.op x := by
  classical
  change (recoveryMagma M).op (square (recoveryMagma M).op x) x = _
  rw [forward_square]
  change (if square M.op (square M.op x) = square M.op x then rightCube M.op x
    else forwardInverse (leftCube M.op) (rightCube M.op x)) = _
  split_ifs with hq
  · exact CubeConditional.cubes_eq_of_square_idempotent M h x hq
  · rw [forwardInverse, if_pos (rightCube_mem_image M h x)]
    exact CubeConditional.leftCube_rightCube M h x

theorem forward_law : @Equation3545 G (recoveryMagma M) := by
  classical
  intro x y
  change (recoveryMagma M).op x y =
    (recoveryMagma M).op y (rightCube (recoveryMagma M).op x)
  rw [forward_rightCube M h]
  change (if square M.op x = square M.op y then _ else _) =
    (if square M.op y = square M.op (leftCube M.op x) then _ else _)
  rw [square_twist M.op (leftCube M.op) h, h x y]
  by_cases he : square M.op x = square M.op y
  · rw [if_pos he, if_pos he.symm]
    rfl
  · rw [if_neg he, if_neg (Ne.symm he)]
    rfl

omit h M [Finite G] in
/-- Extending an image permutation by the identity has the expected inverse. -/
theorem partialInverse_forwardInverse (w : G → G)
    (hs : ∀ {a b}, w (w a) = w (w b) → w a = w b)
    (hr : ∀ z, (∃ a, w a = z) → ∃ a, w (w a) = z) (z : G) :
    partialInverse w (forwardInverse w z) = z := by
  classical
  by_cases hz : ∃ a, w a = z
  · obtain ⟨a, rfl⟩ := hr z hz
    rw [forwardInverse, if_pos ⟨w a, rfl⟩, partialInverse_twice w hs]
  · have hn : ¬ ∃ a, w (w a) = z := fun ⟨a, ha⟩ => hz ⟨w a, ha⟩
    rw [forwardInverse, if_neg hz, partialInverse, dif_neg hn]

theorem companion_recovery : companionMagma (recoveryMagma M) = M := by
  classical
  have hr : ∀ z, (∃ a, leftCube M.op a = z) → ∃ a, leftCube M.op (leftCube M.op a) = z := by
    intro z hz
    obtain ⟨a, ha⟩ := (leftCube_bijective_image M h).surjective ⟨z, hz⟩
    obtain ⟨b, hb⟩ := a.property
    exact ⟨b, by simpa only [← hb] using congrArg Subtype.val ha⟩
  change Magma.mk _ = Magma.mk M.op
  congr 1
  funext x y
  change companion (recoveryMagma M).op x y = M.op x y
  rw [companion, forward_square, forward_square]
  have hc : rightCube (recoveryMagma M).op = leftCube M.op := funext (forward_rightCube M h)
  rw [hc]
  change (if square M.op x = square M.op y then (recoveryMagma M).op x y
    else partialInverse (leftCube M.op) ((recoveryMagma M).op x y)) = _
  by_cases he : square M.op x = square M.op y
  · rw [if_pos he, forward_apply, if_pos he]
  · rw [if_neg he, forward_apply, if_neg he]
    exact partialInverse_forwardInverse _ (leftCube_kernel_stable M h) hr _

end finite
end CubeForwardStructural

/-- The stable-image cube permutation makes the finite interpretation reversible. -/
theorem Law.MagmaLaw.Equation3545_structuralFromFin_Equation3342_cubeImage :
    Law3545.StructuralFromFin Law3342 := by
  intro G _ M hM
  have h := (@Law3342.models_iff G M).mp hM
  have ht := CubeForwardStructural.forward_law M h
  refine ⟨recoveryMagma M, (@Law3545.models_iff G (recoveryMagma M)).mpr ht, recovery_definable M, ?_⟩
  simpa only [CubeForwardStructural.companion_recovery M h] using
    companion_definable (recoveryMagma M) ht

/-- info: 'Law.MagmaLaw.Equation3545_structuralFromFin_Equation3342_cubeImage' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.Equation3545_structuralFromFin_Equation3342_cubeImage
