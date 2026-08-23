import equational_theories.Definability.QMin

/-!
# Cells refuted by the rationals under `min`

Machine-generated from `Definability/QMin.lean`. Laws `4364` and `4541` hold in
`(ℚ, min)`, so every operation definable there is `min`, `max`, or a projection; each
target below fails in all four, with the counterexample recorded in the proof.
-/

open Law Law.MagmaLaw Magma

theorem qmin_min_not_313 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law313 := by
  intro hs
  have := (@Law313.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_313 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law313 := by
  intro hs
  have := (@Law313.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_313 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law313 := by
  intro hs
  have := (@Law313.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_313 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law313 := by
  intro hs
  have := (@Law313.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation313_not_definableFrom_Equation4364 :
    ¬ Law313.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_313 qmin_max_not_313 qmin_p1_not_313 qmin_p2_not_313

theorem Equation313_not_definableFrom_Equation4541 :
    ¬ Law313.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_313 qmin_max_not_313 qmin_p1_not_313 qmin_p2_not_313

theorem qmin_min_not_504 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law504 := by
  intro hs
  have := (@Law504.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_504 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law504 := by
  intro hs
  have := (@Law504.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_504 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law504 := by
  intro hs
  have := (@Law504.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_504 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law504 := by
  intro hs
  have := (@Law504.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation504_not_definableFrom_Equation4364 :
    ¬ Law504.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_504 qmin_max_not_504 qmin_p1_not_504 qmin_p2_not_504

theorem Equation504_not_definableFrom_Equation4541 :
    ¬ Law504.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_504 qmin_max_not_504 qmin_p1_not_504 qmin_p2_not_504

theorem qmin_min_not_910 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law910 := by
  intro hs
  have := (@Law910.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_910 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law910 := by
  intro hs
  have := (@Law910.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_910 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law910 := by
  intro hs
  have := (@Law910.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_910 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law910 := by
  intro hs
  have := (@Law910.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation910_not_definableFrom_Equation4364 :
    ¬ Law910.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_910 qmin_max_not_910 qmin_p1_not_910 qmin_p2_not_910

theorem Equation910_not_definableFrom_Equation4541 :
    ¬ Law910.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_910 qmin_max_not_910 qmin_p1_not_910 qmin_p2_not_910

theorem qmin_min_not_1479 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law1479 := by
  intro hs
  have := (@Law1479.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_1479 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law1479 := by
  intro hs
  have := (@Law1479.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_1479 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law1479 := by
  intro hs
  have := (@Law1479.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_1479 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law1479 := by
  intro hs
  have := (@Law1479.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation1479_not_definableFrom_Equation4364 :
    ¬ Law1479.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_1479 qmin_max_not_1479 qmin_p1_not_1479 qmin_p2_not_1479

theorem Equation1479_not_definableFrom_Equation4541 :
    ¬ Law1479.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_1479 qmin_max_not_1479 qmin_p1_not_1479 qmin_p2_not_1479

theorem qmin_min_not_1519 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law1519 := by
  intro hs
  have := (@Law1519.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_1519 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law1519 := by
  intro hs
  have := (@Law1519.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_1519 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law1519 := by
  intro hs
  have := (@Law1519.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_1519 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law1519 := by
  intro hs
  have := (@Law1519.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation1519_not_definableFrom_Equation4364 :
    ¬ Law1519.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_1519 qmin_max_not_1519 qmin_p1_not_1519 qmin_p2_not_1519

theorem Equation1519_not_definableFrom_Equation4541 :
    ¬ Law1519.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_1519 qmin_max_not_1519 qmin_p1_not_1519 qmin_p2_not_1519

theorem qmin_min_not_1722 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law1722 := by
  intro hs
  have := (@Law1722.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_1722 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law1722 := by
  intro hs
  have := (@Law1722.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_1722 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law1722 := by
  intro hs
  have := (@Law1722.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_1722 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law1722 := by
  intro hs
  have := (@Law1722.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation1722_not_definableFrom_Equation4364 :
    ¬ Law1722.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_1722 qmin_max_not_1722 qmin_p1_not_1722 qmin_p2_not_1722

theorem Equation1722_not_definableFrom_Equation4541 :
    ¬ Law1722.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_1722 qmin_max_not_1722 qmin_p1_not_1722 qmin_p2_not_1722

theorem qmin_min_not_3269 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3269 := by
  intro hs
  have := (@Law3269.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3269 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3269 := by
  intro hs
  have := (@Law3269.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3269 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3269 := by
  intro hs
  have := (@Law3269.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_3269 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3269 := by
  intro hs
  have := (@Law3269.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation3269_not_definableFrom_Equation4364 :
    ¬ Law3269.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3269 qmin_max_not_3269 qmin_p1_not_3269 qmin_p2_not_3269

theorem Equation3269_not_definableFrom_Equation4541 :
    ¬ Law3269.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3269 qmin_max_not_3269 qmin_p1_not_3269 qmin_p2_not_3269

theorem qmin_min_not_3272 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3272 := by
  intro hs
  have := (@Law3272.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3272 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3272 := by
  intro hs
  have := (@Law3272.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3272 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3272 := by
  intro hs
  have := (@Law3272.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_3272 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3272 := by
  intro hs
  have := (@Law3272.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation3272_not_definableFrom_Equation4364 :
    ¬ Law3272.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3272 qmin_max_not_3272 qmin_p1_not_3272 qmin_p2_not_3272

theorem Equation3272_not_definableFrom_Equation4541 :
    ¬ Law3272.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3272 qmin_max_not_3272 qmin_p1_not_3272 qmin_p2_not_3272

theorem qmin_min_not_3279 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3279 := by
  intro hs
  have := (@Law3279.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3279 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3279 := by
  intro hs
  have := (@Law3279.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3279 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3279 := by
  intro hs
  have := (@Law3279.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_3279 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3279 := by
  intro hs
  have := (@Law3279.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation3279_not_definableFrom_Equation4364 :
    ¬ Law3279.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3279 qmin_max_not_3279 qmin_p1_not_3279 qmin_p2_not_3279

theorem Equation3279_not_definableFrom_Equation4541 :
    ¬ Law3279.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3279 qmin_max_not_3279 qmin_p1_not_3279 qmin_p2_not_3279

theorem qmin_min_not_3364 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3364 := by
  intro hs
  have := (@Law3364.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3364 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3364 := by
  intro hs
  have := (@Law3364.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3364 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3364 := by
  intro hs
  have := (@Law3364.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1 0
  norm_num [Magma.op] at this

theorem qmin_p2_not_3364 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3364 := by
  intro hs
  have := (@Law3364.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem Equation3364_not_definableFrom_Equation4364 :
    ¬ Law3364.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3364 qmin_max_not_3364 qmin_p1_not_3364 qmin_p2_not_3364

theorem Equation3364_not_definableFrom_Equation4541 :
    ¬ Law3364.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3364 qmin_max_not_3364 qmin_p1_not_3364 qmin_p2_not_3364

theorem qmin_min_not_3472 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3472 := by
  intro hs
  have := (@Law3472.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3472 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3472 := by
  intro hs
  have := (@Law3472.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3472 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3472 := by
  intro hs
  have := (@Law3472.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_3472 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3472 := by
  intro hs
  have := (@Law3472.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation3472_not_definableFrom_Equation4364 :
    ¬ Law3472.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3472 qmin_max_not_3472 qmin_p1_not_3472 qmin_p2_not_3472

theorem Equation3472_not_definableFrom_Equation4541 :
    ¬ Law3472.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3472 qmin_max_not_3472 qmin_p1_not_3472 qmin_p2_not_3472

theorem qmin_min_not_3475 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3475 := by
  intro hs
  have := (@Law3475.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3475 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3475 := by
  intro hs
  have := (@Law3475.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3475 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3475 := by
  intro hs
  have := (@Law3475.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_3475 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3475 := by
  intro hs
  have := (@Law3475.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation3475_not_definableFrom_Equation4364 :
    ¬ Law3475.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3475 qmin_max_not_3475 qmin_p1_not_3475 qmin_p2_not_3475

theorem Equation3475_not_definableFrom_Equation4541 :
    ¬ Law3475.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3475 qmin_max_not_3475 qmin_p1_not_3475 qmin_p2_not_3475

theorem qmin_min_not_3482 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3482 := by
  intro hs
  have := (@Law3482.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3482 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3482 := by
  intro hs
  have := (@Law3482.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3482 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3482 := by
  intro hs
  have := (@Law3482.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_3482 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3482 := by
  intro hs
  have := (@Law3482.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation3482_not_definableFrom_Equation4364 :
    ¬ Law3482.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3482 qmin_max_not_3482 qmin_p1_not_3482 qmin_p2_not_3482

theorem Equation3482_not_definableFrom_Equation4541 :
    ¬ Law3482.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3482 qmin_max_not_3482 qmin_p1_not_3482 qmin_p2_not_3482

theorem qmin_min_not_3588 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3588 := by
  intro hs
  have := (@Law3588.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3588 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3588 := by
  intro hs
  have := (@Law3588.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3588 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3588 := by
  intro hs
  have := (@Law3588.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_3588 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3588 := by
  intro hs
  have := (@Law3588.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem Equation3588_not_definableFrom_Equation4364 :
    ¬ Law3588.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3588 qmin_max_not_3588 qmin_p1_not_3588 qmin_p2_not_3588

theorem Equation3588_not_definableFrom_Equation4541 :
    ¬ Law3588.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3588 qmin_max_not_3588 qmin_p1_not_3588 qmin_p2_not_3588

theorem qmin_min_not_3607 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3607 := by
  intro hs
  have := (@Law3607.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3607 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3607 := by
  intro hs
  have := (@Law3607.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3607 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3607 := by
  intro hs
  have := (@Law3607.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_3607 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3607 := by
  intro hs
  have := (@Law3607.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1 0
  norm_num [Magma.op] at this

theorem Equation3607_not_definableFrom_Equation4364 :
    ¬ Law3607.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3607 qmin_max_not_3607 qmin_p1_not_3607 qmin_p2_not_3607

theorem Equation3607_not_definableFrom_Equation4541 :
    ¬ Law3607.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3607 qmin_max_not_3607 qmin_p1_not_3607 qmin_p2_not_3607

theorem qmin_min_not_3620 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3620 := by
  intro hs
  have := (@Law3620.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3620 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3620 := by
  intro hs
  have := (@Law3620.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3620 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3620 := by
  intro hs
  have := (@Law3620.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_3620 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3620 := by
  intro hs
  have := (@Law3620.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1 0
  norm_num [Magma.op] at this

theorem Equation3620_not_definableFrom_Equation4364 :
    ¬ Law3620.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3620 qmin_max_not_3620 qmin_p1_not_3620 qmin_p2_not_3620

theorem Equation3620_not_definableFrom_Equation4541 :
    ¬ Law3620.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3620 qmin_max_not_3620 qmin_p1_not_3620 qmin_p2_not_3620

theorem qmin_min_not_3675 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law3675 := by
  intro hs
  have := (@Law3675.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_3675 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law3675 := by
  intro hs
  have := (@Law3675.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_3675 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law3675 := by
  intro hs
  have := (@Law3675.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_3675 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law3675 := by
  intro hs
  have := (@Law3675.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation3675_not_definableFrom_Equation4364 :
    ¬ Law3675.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_3675 qmin_max_not_3675 qmin_p1_not_3675 qmin_p2_not_3675

theorem Equation3675_not_definableFrom_Equation4541 :
    ¬ Law3675.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_3675 qmin_max_not_3675 qmin_p1_not_3675 qmin_p2_not_3675

theorem qmin_min_not_4273 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law4273 := by
  intro hs
  have := (@Law4273.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0
  norm_num [Magma.op] at this

theorem qmin_max_not_4273 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law4273 := by
  intro hs
  have := (@Law4273.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_4273 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law4273 := by
  intro hs
  have := (@Law4273.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_4273 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law4273 := by
  intro hs
  have := (@Law4273.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1
  norm_num [Magma.op] at this

theorem Equation4273_not_definableFrom_Equation4364 :
    ¬ Law4273.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_4273 qmin_max_not_4273 qmin_p1_not_4273 qmin_p2_not_4273

theorem Equation4273_not_definableFrom_Equation4541 :
    ¬ Law4273.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_4273 qmin_max_not_4273 qmin_p1_not_4273 qmin_p2_not_4273

theorem qmin_min_not_4415 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ min x y⟩ Law4415 := by
  intro hs
  have := (@Law4415.models_iff ℚ ⟨fun x y : ℚ ↦ min x y⟩).mp hs 1 0 1
  norm_num [Magma.op] at this

theorem qmin_max_not_4415 : ¬ @satisfies _ ℚ ⟨fun x y : ℚ ↦ max x y⟩ Law4415 := by
  intro hs
  have := (@Law4415.models_iff ℚ ⟨fun x y : ℚ ↦ max x y⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem qmin_p1_not_4415 : ¬ @satisfies _ ℚ ⟨fun x _ : ℚ ↦ x⟩ Law4415 := by
  intro hs
  have := (@Law4415.models_iff ℚ ⟨fun x _ : ℚ ↦ x⟩).mp hs 0 0 1
  norm_num [Magma.op] at this

theorem qmin_p2_not_4415 : ¬ @satisfies _ ℚ ⟨fun _ y : ℚ ↦ y⟩ Law4415 := by
  intro hs
  have := (@Law4415.models_iff ℚ ⟨fun _ y : ℚ ↦ y⟩).mp hs 0 1 0
  norm_num [Magma.op] at this

theorem Equation4415_not_definableFrom_Equation4364 :
    ¬ Law4415.DefinableFrom Law4364 :=
  not_definableFrom_minMagma ((@Law4364.models_iff ℚ minMagma).mpr minMagma_4364)
    qmin_min_not_4415 qmin_max_not_4415 qmin_p1_not_4415 qmin_p2_not_4415

theorem Equation4415_not_definableFrom_Equation4541 :
    ¬ Law4415.DefinableFrom Law4541 :=
  not_definableFrom_minMagma ((@Law4541.models_iff ℚ minMagma).mpr minMagma_4541)
    qmin_min_not_4415 qmin_max_not_4415 qmin_p1_not_4415 qmin_p2_not_4415
