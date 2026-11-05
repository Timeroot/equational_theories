import equational_theories.Parastrophes.Attributes
import equational_theories.Generated.Greedy.Eq466
import equational_theories.Generated.Greedy.Eq474
import equational_theories.Generated.Greedy.Eq503
import equational_theories.Generated.Greedy.Eq676
import equational_theories.Generated.Greedy.Eq677
import equational_theories.Generated.Greedy.Eq679
import equational_theories.Generated.Greedy.Eq704
import equational_theories.Generated.Greedy.Eq706
import equational_theories.Generated.Greedy.Eq872
import equational_theories.Generated.Greedy.Eq882
import equational_theories.Generated.Greedy.Eq907
import equational_theories.Generated.Greedy.Eq1119
import equational_theories.Generated.Greedy.Eq1279
import equational_theories.Generated.Greedy.Eq1312

/-! Countable countermodels obtained by completing finite tables with
prescribed row or column collisions. -/
namespace Parastrophes.Catalogue

private noncomputable def rowCollision503 : Eq503.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- The partial table `0*1 = 0*2 = 3` extends to an infinite E503 model,
so left bijectivity fails on arbitrary carriers. -/
@[parastrophe_result] theorem not_leftQuasigroup503_all_collision :
    ¬ SideQuasigroupLaw .all Law503 .left := by
  intro h
  let e := rowCollision503
  have hQ := h Nat e.toMagma trivial
    ((@Law503.models_iff Nat e.toMagma).mpr e.toMagma_equation503)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision503; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision503; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

private noncomputable def rowCollision677 : Eq677.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- The partial table `0*1 = 0*2 = 3` extends to an infinite E677 model,
so left bijectivity fails on arbitrary carriers. -/
@[parastrophe_result] theorem not_leftQuasigroup677_all_collision :
    ¬ SideQuasigroupLaw .all Law677 .left := by
  intro h
  let e := rowCollision677
  have hQ := h Nat e.toMagma trivial
    ((@Law677.models_iff Nat e.toMagma).mpr e.toMagma_equation677)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision677; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision677; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- The original E677 countermodel already contains a column collision,
`1*1 = 2*1 = 2`. Thus neither side is universally bijective on arbitrary carriers. -/
@[parastrophe_result] theorem not_rightQuasigroup677_all_collision :
    ¬ SideQuasigroupLaw .all Law677 .right := by
  intro h
  let e := Eq677.PartialSolution.counter255
  have hQ := h Nat e.toMagma trivial
    ((@Law677.models_iff Nat e.toMagma).mpr e.toMagma_equation677)
  have h1 := e.of_R 1 1 2 (by unfold e Eq677.PartialSolution.counter255; decide)
  have h2 := e.of_R 2 1 2 (by unfold e Eq677.PartialSolution.counter255; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 1).1 (h1.trans h2.symm))

private noncomputable def collisions907 : Eq907.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3), (2, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

private noncomputable def rowCollision882 : Eq882.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- The partial table `0*1 = 0*2 = 3` extends to an infinite E882 model. -/
@[parastrophe_result] theorem not_leftQuasigroup882_all_collision :
    ¬ SideQuasigroupLaw .all Law882 .left := by
  intro h
  let e := rowCollision882
  have hQ := h Nat e.toMagma trivial
    ((@Law882.models_iff Nat e.toMagma).mpr e.toMagma_equation882)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision882; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision882; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- An E907 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup907_all_collision :
    ¬ SideQuasigroupLaw .all Law907 .left := by
  intro h
  let e := collisions907
  have hQ := h Nat e.toMagma trivial
    ((@Law907.models_iff Nat e.toMagma).mpr e.toMagma_equation907)
  have h1 := e.of_R 0 1 3 (by unfold e collisions907; decide)
  have h2 := e.of_R 0 2 3 (by unfold e collisions907; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- The same E907 magma also retains the column collision `0*1 = 2*1`. -/
@[parastrophe_result] theorem not_rightQuasigroup907_all_collision :
    ¬ SideQuasigroupLaw .all Law907 .right := by
  intro h
  let e := collisions907
  have hQ := h Nat e.toMagma trivial
    ((@Law907.models_iff Nat e.toMagma).mpr e.toMagma_equation907)
  have h1 := e.of_R 0 1 3 (by unfold e collisions907; decide)
  have h2 := e.of_R 2 1 3 (by unfold e collisions907; decide)
  exact (by decide : (0 : Nat) ≠ 2) ((hQ 1).1 (h1.trans h2.symm))

private noncomputable def rowCollision676 : Eq676.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- An E676 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup676_all_collision :
    ¬ SideQuasigroupLaw .all Law676 .left := by
  intro h
  let e := rowCollision676
  have hQ := h Nat e.toMagma trivial
    ((@Law676.models_iff Nat e.toMagma).mpr e.toMagma_equation676)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision676; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision676; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

private noncomputable def rowCollision706 : Eq706.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- An E706 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup706_all_collision :
    ¬ SideQuasigroupLaw .all Law706 .left := by
  intro h
  let e := rowCollision706
  have hQ := h Nat e.toMagma trivial
    ((@Law706.models_iff Nat e.toMagma).mpr e.toMagma_equation706)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision706; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision706; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

private noncomputable def rowCollision679 : Eq679.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- An E679 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup679_all_collision :
    ¬ SideQuasigroupLaw .all Law679 .left := by
  intro h
  let e := rowCollision679
  have hQ := h Nat e.toMagma trivial
    ((@Law679.models_iff Nat e.toMagma).mpr e.toMagma_equation679)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision679; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision679; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

private noncomputable def rowCollision872 : Eq872.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- An E872 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup872_all_collision :
    ¬ SideQuasigroupLaw .all Law872 .left := by
  intro h
  let e := rowCollision872
  have hQ := h Nat e.toMagma trivial
    ((@Law872.models_iff Nat e.toMagma).mpr e.toMagma_equation872)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision872; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision872; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

private noncomputable def rowCollision704 : Eq704.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3), (2, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- An E704 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup704_all_collision :
    ¬ SideQuasigroupLaw .all Law704 .left := by
  intro h
  let e := rowCollision704
  have hQ := h Nat e.toMagma trivial
    ((@Law704.models_iff Nat e.toMagma).mpr e.toMagma_equation704)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision704; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision704; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- The same E704 model also retains the column collision `0*1 = 2*1`. -/
@[parastrophe_result] theorem not_rightQuasigroup704_all_collision :
    ¬ SideQuasigroupLaw .all Law704 .right := by
  intro h
  let e := rowCollision704
  have hQ := h Nat e.toMagma trivial
    ((@Law704.models_iff Nat e.toMagma).mpr e.toMagma_equation704)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision704; decide)
  have h2 := e.of_R 2 1 3 (by unfold e rowCollision704; decide)
  exact (by decide : (0 : Nat) ≠ 2) ((hQ 1).1 (h1.trans h2.symm))

private noncomputable def rowCollision466 : Eq466.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- An E466 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup466_all_collision :
    ¬ SideQuasigroupLaw .all Law466 .left := by
  intro h
  let e := rowCollision466
  have hQ := h Nat e.toMagma trivial
    ((@Law466.models_iff Nat e.toMagma).mpr e.toMagma_equation466)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision466; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision466; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

private noncomputable def rowCollision474 : Eq474.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  rule_7 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- An E474 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup474_all_collision :
    ¬ SideQuasigroupLaw .all Law474 .left := by
  intro h
  let e := rowCollision474
  have hQ := h Nat e.toMagma trivial
    ((@Law474.models_iff Nat e.toMagma).mpr e.toMagma_equation474)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision474; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision474; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

private noncomputable def rowCollision1312 : Eq1312.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  rule_7 := by simp only [← imp_iff_not_or]; aesop
  rule_8 := by simp only [← imp_iff_not_or]; aesop
  rule_9 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- An E1312 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup1312_all_collision :
    ¬ SideQuasigroupLaw .all Law1312 .left := by
  intro h
  let e := rowCollision1312
  have hQ := h Nat e.toMagma trivial
    ((@Law1312.models_iff Nat e.toMagma).mpr e.toMagma_equation1312)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision1312; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision1312; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

private noncomputable def rowCollision1279 : Eq1279.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3), (2, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- An E1279 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup1279_all_collision :
    ¬ SideQuasigroupLaw .all Law1279 .left := by
  intro h
  let e := rowCollision1279
  have hQ := h Nat e.toMagma trivial
    ((@Law1279.models_iff Nat e.toMagma).mpr e.toMagma_equation1279)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision1279; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision1279; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

private noncomputable def rowCollision1119 : Eq1119.PartialSolution Nat where
  R x y z := (x, y, z) ∈ ({(0, 1, 3), (0, 2, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  rule_7 := by simp only [← imp_iff_not_or]; aesop
  rule_8 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {0, 1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

/-- An E1119 magma on the natural numbers retains the collision `0*1 = 0*2`. -/
@[parastrophe_result] theorem not_leftQuasigroup1119_all_collision :
    ¬ SideQuasigroupLaw .all Law1119 .left := by
  intro h
  let e := rowCollision1119
  have hQ := h Nat e.toMagma trivial
    ((@Law1119.models_iff Nat e.toMagma).mpr e.toMagma_equation1119)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision1119; decide)
  have h2 := e.of_R 0 2 3 (by unfold e rowCollision1119; decide)
  exact (by decide : (1 : Nat) ≠ 2) ((hQ 0).1 (h1.trans h2.symm))

/-- The same E1279 model also retains the column collision `0*1 = 2*1`. -/
@[parastrophe_result] theorem not_rightQuasigroup1279_all_collision :
    ¬ SideQuasigroupLaw .all Law1279 .right := by
  intro h
  let e := rowCollision1279
  have hQ := h Nat e.toMagma trivial
    ((@Law1279.models_iff Nat e.toMagma).mpr e.toMagma_equation1279)
  have h1 := e.of_R 0 1 3 (by unfold e rowCollision1279; decide)
  have h2 := e.of_R 2 1 3 (by unfold e rowCollision1279; decide)
  exact (by decide : (0 : Nat) ≠ 2) ((hQ 1).1 (h1.trans h2.symm))

end Parastrophes.Catalogue
