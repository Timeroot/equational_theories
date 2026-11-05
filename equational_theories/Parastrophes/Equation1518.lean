import equational_theories.Parastrophes.Attributes
import equational_theories.ManuallyProved.Equation1518

/-! Square translations settle the finite left-quasigroup question. The
established free-group countermodel refutes the corresponding infinite claim. -/
namespace Parastrophes.Catalogue
open Eq1518.Greedy

/-- In E1518, the translation indexed by a square maps its square root to itself. -/
theorem square_mul1518 {G : Type} (M : Magma G) (h : @Equation1518 G M) (y : G) :
    M.op (M.op y y) y = M.op y y := by
  have hh := h (M.op y y) y
  rw [← h y y] at hh
  exact hh.symm

/-- Finding the inverse square is equivalent to finding a fixed point of
`y ↦ x*(y*x)`. This equivalence does not require finiteness or cancellation. -/
theorem cross_fixed_iff_square1518 {G : Type} (M : Magma G)
    (h : @Equation1518 G M) (x y : G) :
    M.op x (M.op y x) = y ↔ M.op y y = x := by
  constructor
  · intro hf
    have hh := h x y
    rw [hf, square_mul1518 M h y] at hh
    exact hh.symm
  · intro hs
    have hh := h y y
    rw [hs] at hh
    exact hh.symm

/-- Square translations are onto, hence injective on a finite carrier.
Since `(y*y)*y = y*y`, equal squares have equal roots. The square map is
therefore a permutation, so every translation is indexed by a square. -/
@[parastrophe_result] theorem leftQuasigroup1518_fin :
    SideQuasigroupLaw .fin Law1518 .left := by
  intro G M hG hM
  letI : Finite G := hG
  have h := (@Law1518.models_iff G M).mp hM
  have hs (y : G) : Function.Surjective (M.op (M.op y y)) :=
    fun x => ⟨M.op x (M.op y x), (h x y).symm⟩
  have hi (y : G) := Finite.injective_iff_surjective.mpr (hs y)
  have sqi : Function.Injective (fun y => M.op y y) := by
    intro y z he
    change M.op y y = M.op z z at he
    apply hi y
    rw [square_mul1518 M h y, he, square_mul1518 M h z]
  have sqs := Finite.injective_iff_surjective.mp sqi
  intro y
  obtain ⟨z, rfl⟩ := sqs y
  exact ⟨hi z, hs z⟩

/-- The existing E1518 construction sends two distinct free-group words to
`of 1` inverse in its identity row. -/
@[parastrophe_result] theorem not_leftQuasigroup1518_all :
    ¬ SideQuasigroupLaw .all Law1518 .left := by
  intro h
  let e : Extension := ⟨fromList E0List, fromList_ok⟩
  have hQ := h (GreedyMagma e) inferInstance trivial
    ((@Law1518.models_iff _ _).mpr (eq1518 e))
  let a : FreeGroup Nat := FreeGroup.of 2 * (FreeGroup.of 1)⁻¹
  let b : FreeGroup Nat := FreeGroup.of 3 * (FreeGroup.of 1)^(-2 : ℤ)
  have he : @Magma.op (GreedyMagma e) _ (1 : FreeGroup Nat) a = @Magma.op (GreedyMagma e) _ (1 : FreeGroup Nat) b := by
    change f e (a * 1⁻¹) * 1 = f e (b * 1⁻¹) * 1
    simp only [inv_one, mul_one]
    rw [fromList_eval (e := e) rfl a ((FreeGroup.of 1)⁻¹),
      fromList_eval (e := e) rfl b ((FreeGroup.of 1)⁻¹)]
  have hab := (hQ (1 : FreeGroup Nat)).1 he
  exact (by decide : a ≠ b) hab

end Parastrophes.Catalogue
