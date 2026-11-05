import equational_theories.Parastrophes.Attributes
import equational_theories.Generated.Greedy.Eq1278

/-!
# An infinite E1278 model with a noninjective left translation

The two products `0 * 1 = 3` and `0 * 2 = 3` satisfy the partial-table
invariants of the E1278 greedy completion. Their completion retains this
collision, even though its squaring map is injective.
-/

namespace Parastrophes.Catalogue

open Law

private noncomputable def rowCollision1278 : Eq1278.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_12 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- E1278 does not force left bijectivity on arbitrary carriers. -/
@[parastrophe_result] theorem not_leftQuasigroup1278_all_collision :
    ¬ SideQuasigroupLaw .all Law1278 .left := by
  intro h
  let e := rowCollision1278
  have hQ := h Nat e.toMagma trivial
    ((@Law1278.models_iff Nat e.toMagma).mpr e.toMagma_equation1278)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision1278; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision1278; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

end Parastrophes.Catalogue
