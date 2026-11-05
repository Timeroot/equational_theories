import equational_theories.Parastrophes.Equation1518
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate

/-!
# E1518 square maps can have cycles longer than three or twelve

The existing 15-element example in `Generated/All4x4Tables/Refutation939.lean`
already has a twelve-cycle under squaring. It must be included in research
samples: the small models used in an earlier search missed this example.

A small additive extension triples that cycle. If B satisfies E1518, put
`(i,u) * (j,v) = (B(i,j), v + c(i,j))`. The source identity holds exactly
when the three offsets along its right branch add to zero. These are linear
conditions on c, not checks over all pairs in the enlarged model. The offset
below has sum one around the seed's twelve-cycle, so the lift has a 36-cycle.

These examples refute proposed bounds on the square map. They do not refute
uniform term recovery, whose term need not be a power of the square map.
-/
namespace Parastrophes.Eq1518SquareCycles

/-- A central additive extension; only the second fibre coordinate is used. -/
@[implicit_reducible] def extension {B A : Type} [AddCommGroup A]
    (M : Magma B) (c : B → B → A) :
    Magma (B × A) := ⟨fun x y => (M.op x.1 y.1, y.2 + c x.1 y.1)⟩

/-- Nine or 225 linear equations on the base can replace a much larger model
check. This theorem works for every additive abelian group. -/
theorem extension_law {B A : Type} [AddCommGroup A] (M : Magma B)
    (h : @Equation1518 B M) (c : B → B → A)
    (hc : ∀ x y, c y x + c x (M.op y x) +
      c (M.op y y) (M.op x (M.op y x)) = 0) :
    @Equation1518 (B × A) (extension M c) := by
  intro x y
  apply Prod.ext
  · exact h x.1 y.1
  · change x.2 = ((x.2 + c y.1 x.1) + c x.1 (M.op y.1 x.1)) +
      c (M.op y.1 y.1) (M.op x.1 (M.op y.1 x.1))
    rw [add_assoc, add_assoc, ← add_assoc (c y.1 x.1), hc, add_zero]

/-- In an additive extension, one application of `y ↦ x*(y*x)` repairs the
fibre coordinate of any square root in the base. The inner multiplication
already discards the fibre coordinate of y. Thus a term which recovers square
roots downstairs acquires a square-root term upstairs by adding two operations.
This does not give a uniform bound over towers of extensions. -/
theorem extension_cross_square {B A : Type} [AddCommGroup A]
    (M : Magma B) (h : @Equation1518 B M) (c : B → B → A)
    (hc : ∀ x y, c y x + c x (M.op y x) +
      c (M.op y y) (M.op x (M.op y x)) = 0)
    (x y : B × A) (hy : M.op y.1 y.1 = x.1) :
    let N := extension M c
    let z := N.op x (N.op y x)
    N.op z z = x := by
  let N := extension M c
  let r : B × A := (y.1, x.2 - c y.1 y.1)
  have hr : N.op r r = x := by
    apply Prod.ext
    · exact hy
    · change x.2 - c y.1 y.1 + c y.1 y.1 = x.2
      exact sub_add_cancel _ _
  have hf := (Catalogue.cross_fixed_iff_square1518 N
    (extension_law M h c hc) x r).2 hr
  have he : N.op x (N.op y x) = N.op x (N.op r x) := rfl
  change N.op (N.op x (N.op y x)) (N.op x (N.op y x)) = x
  rw [he, hf]
  exact hr

/-- The previously recorded E1518 model, with a short stable name. -/
@[implicit_reducible] def seed : Magma (Fin 15) := ⟨fun x y =>
  (![
    ![1, 12, 13, 7, 2, 9, 4, 8, 3, 14, 5, 0, 6, 10, 11],
    ![1, 2, 13, 14, 8, 3, 10, 5, 9, 4, 12, 6, 0, 7, 11],
    ![7, 2, 3, 14, 12, 9, 4, 11, 6, 10, 5, 13, 0, 1, 8],
    ![14, 8, 3, 4, 12, 13, 10, 5, 0, 7, 11, 6, 9, 1, 2],
    ![7, 12, 9, 4, 5, 13, 14, 11, 6, 1, 8, 0, 3, 10, 2],
    ![1, 8, 13, 10, 5, 6, 14, 12, 0, 7, 2, 9, 3, 4, 11],
    ![10, 2, 9, 14, 11, 6, 7, 12, 13, 1, 8, 3, 0, 4, 5],
    ![4, 11, 3, 10, 12, 0, 7, 8, 13, 14, 2, 9, 6, 1, 5],
    ![10, 5, 0, 4, 11, 13, 1, 8, 9, 14, 12, 3, 6, 7, 2],
    ![4, 11, 6, 1, 5, 0, 14, 2, 9, 10, 12, 13, 3, 7, 8],
    ![14, 5, 0, 7, 2, 6, 1, 12, 3, 10, 11, 13, 9, 4, 8],
    ![14, 12, 6, 1, 8, 3, 7, 2, 13, 4, 11, 0, 9, 10, 5],
    ![4, 11, 9, 7, 2, 0, 10, 5, 3, 1, 8, 6, 13, 14, 12],
    ![7, 5, 0, 10, 8, 3, 1, 11, 6, 4, 2, 9, 13, 14, 12],
    ![10, 8, 6, 1, 11, 9, 4, 2, 0, 7, 5, 3, 13, 14, 12]] : Fin 15 → Fin 15 → Fin 15) x y⟩

theorem seed_law : @Equation1518 (Fin 15) seed := by decide

def square {G : Type} (M : Magma G) (x : G) := M.op x x

/-- The old finite counterexample already rules out the square-cube guess. -/
theorem seed_square_cube : (square seed)^[3] 0 = 3 := by decide

theorem seed_square_period : (square seed)^[12] 0 = 0 := by decide

/-- A solution of the linear offset equations over F3. -/
def offset : Fin 15 → Fin 15 → ZMod 3 := ![
    ![0, 0, 0, 1, 0, 0, 2, 2, 2, 0, 0, 0, 2, 0, 0],
    ![0, 2, 0, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 2, 0],
    ![1, 2, 1, 0, 2, 2, 2, 2, 0, 0, 0, 1, 0, 1, 2],
    ![1, 0, 1, 0, 2, 1, 1, 0, 0, 1, 2, 1, 0, 1, 2],
    ![0, 0, 2, 0, 1, 1, 1, 2, 0, 0, 0, 2, 1, 1, 2],
    ![0, 0, 2, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1],
    ![0, 0, 2, 2, 0, 0, 0, 1, 2, 0, 2, 0, 0, 1, 2],
    ![1, 2, 2, 2, 2, 0, 0, 1, 2, 1, 1, 0, 2, 0, 2],
    ![0, 0, 2, 0, 0, 2, 0, 1, 2, 1, 0, 2, 2, 0, 1],
    ![1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0],
    ![0, 0, 2, 1, 1, 2, 2, 1, 2, 0, 0, 0, 0, 2, 0],
    ![0, 0, 1, 1, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 2, 0, 1, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

theorem offset_condition (x y : Fin 15) :
    offset y x + offset x (seed.op y x) +
      offset (seed.op y y) (seed.op x (seed.op y x)) = 0 := by
  revert x y
  decide

@[implicit_reducible] def model45 : Magma (Fin 15 × ZMod 3) := extension seed offset

theorem model45_law : @Equation1518 (Fin 15 × ZMod 3) model45 :=
  extension_law seed seed_law offset offset_condition

/-- One circuit of the seed cycle adds one in the new fibre. -/
theorem square_twelve : (square model45)^[12] (0,0) = (0,1) := by decide

theorem square_thirty_six : (square model45)^[36] (0,0) = (0,0) := by decide

/-- The lifted point has exact period 36, not merely period dividing 36. -/
theorem square_no_shorter : ∀ k : Fin 36, k ≠ 0 →
    (square model45)^[k.val] (0,0) ≠ (0,0) := by decide

end Parastrophes.Eq1518SquareCycles
