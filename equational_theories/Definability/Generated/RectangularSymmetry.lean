import equational_theories.Definability.RectangularSymmetry

/-! Generated from data/definability_rectangular_symmetry.json. -/
open Law Law.MagmaLaw Magma.RectangularSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem target3259 : ∀ a b c,
    @Equation3259 (Fin 16) (family a b c) → (family a b c).IsEndo forbidden := by native_decide

private theorem target3511 : ∀ a b c,
    @Equation3511 (Fin 16) (family a b c) → (family a b c).IsEndo forbidden := by native_decide

theorem Equation3511_not_structuralFromFin_Equation3744_rectangularSymmetry : ¬ Law3511.StructuralFromFin Law3744 := by
  apply refutes 0
  · exact (@Law3744.models_iff (Fin 16) (source 0)).mpr (by native_decide)
  · intro a b c h
    exact target3511 a b c ((@Law3511.models_iff (Fin 16) (family a b c)).mp h)

/-- info: 'Equation3511_not_structuralFromFin_Equation3744_rectangularSymmetry' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3511_not_structuralFromFin_Equation3744_rectangularSymmetry._native.native_decide.ax_1_1, target3511._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_2, classification._native.native_decide.ax_1_3, classification._native.native_decide.ax_1_4, classification._native.native_decide.ax_1_5, classification._native.native_decide.ax_1_6, classification._native.native_decide.ax_1_7, classification._native.native_decide.ax_1_8, classification._native.native_decide.ax_1_9, forbiddenPerm._native.native_decide.ax_1, perm._native.native_decide.ax_1, source_endos._native.native_decide.ax_1_1, source_not_endo._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3511_not_structuralFromFin_Equation3744_rectangularSymmetry

theorem Equation3259_not_structuralFromFin_Equation3744_rectangularSymmetry : ¬ Law3259.StructuralFromFin Law3744 := by
  apply refutes 0
  · exact (@Law3744.models_iff (Fin 16) (source 0)).mpr (by native_decide)
  · intro a b c h
    exact target3259 a b c ((@Law3259.models_iff (Fin 16) (family a b c)).mp h)

/-- info: 'Equation3259_not_structuralFromFin_Equation3744_rectangularSymmetry' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3259_not_structuralFromFin_Equation3744_rectangularSymmetry._native.native_decide.ax_1_1, target3259._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_2, classification._native.native_decide.ax_1_3, classification._native.native_decide.ax_1_4, classification._native.native_decide.ax_1_5, classification._native.native_decide.ax_1_6, classification._native.native_decide.ax_1_7, classification._native.native_decide.ax_1_8, classification._native.native_decide.ax_1_9, forbiddenPerm._native.native_decide.ax_1, perm._native.native_decide.ax_1, source_endos._native.native_decide.ax_1_1, source_not_endo._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3259_not_structuralFromFin_Equation3744_rectangularSymmetry

theorem Equation3511_not_structuralFromFin_Equation1465_rectangularSymmetry : ¬ Law3511.StructuralFromFin Law1465 := by
  apply refutes 0
  · exact (@Law1465.models_iff (Fin 16) (source 0)).mpr (by native_decide)
  · intro a b c h
    exact target3511 a b c ((@Law3511.models_iff (Fin 16) (family a b c)).mp h)

/-- info: 'Equation3511_not_structuralFromFin_Equation1465_rectangularSymmetry' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3511_not_structuralFromFin_Equation1465_rectangularSymmetry._native.native_decide.ax_1_1, target3511._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_2, classification._native.native_decide.ax_1_3, classification._native.native_decide.ax_1_4, classification._native.native_decide.ax_1_5, classification._native.native_decide.ax_1_6, classification._native.native_decide.ax_1_7, classification._native.native_decide.ax_1_8, classification._native.native_decide.ax_1_9, forbiddenPerm._native.native_decide.ax_1, perm._native.native_decide.ax_1, source_endos._native.native_decide.ax_1_1, source_not_endo._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3511_not_structuralFromFin_Equation1465_rectangularSymmetry

theorem Equation3511_not_structuralFromFin_Equation428_rectangularSymmetry : ¬ Law3511.StructuralFromFin Law428 := by
  apply refutes 1
  · exact (@Law428.models_iff (Fin 16) (source 1)).mpr (by native_decide)
  · intro a b c h
    exact target3511 a b c ((@Law3511.models_iff (Fin 16) (family a b c)).mp h)

/-- info: 'Equation3511_not_structuralFromFin_Equation428_rectangularSymmetry' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3511_not_structuralFromFin_Equation428_rectangularSymmetry._native.native_decide.ax_1_1, target3511._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_2, classification._native.native_decide.ax_1_3, classification._native.native_decide.ax_1_4, classification._native.native_decide.ax_1_5, classification._native.native_decide.ax_1_6, classification._native.native_decide.ax_1_7, classification._native.native_decide.ax_1_8, classification._native.native_decide.ax_1_9, forbiddenPerm._native.native_decide.ax_1, perm._native.native_decide.ax_1, source_endos._native.native_decide.ax_1_1, source_not_endo._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3511_not_structuralFromFin_Equation428_rectangularSymmetry

theorem Equation3259_not_structuralFromFin_Equation1465_rectangularSymmetry : ¬ Law3259.StructuralFromFin Law1465 := by
  apply refutes 0
  · exact (@Law1465.models_iff (Fin 16) (source 0)).mpr (by native_decide)
  · intro a b c h
    exact target3259 a b c ((@Law3259.models_iff (Fin 16) (family a b c)).mp h)

/-- info: 'Equation3259_not_structuralFromFin_Equation1465_rectangularSymmetry' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3259_not_structuralFromFin_Equation1465_rectangularSymmetry._native.native_decide.ax_1_1, target3259._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_2, classification._native.native_decide.ax_1_3, classification._native.native_decide.ax_1_4, classification._native.native_decide.ax_1_5, classification._native.native_decide.ax_1_6, classification._native.native_decide.ax_1_7, classification._native.native_decide.ax_1_8, classification._native.native_decide.ax_1_9, forbiddenPerm._native.native_decide.ax_1, perm._native.native_decide.ax_1, source_endos._native.native_decide.ax_1_1, source_not_endo._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3259_not_structuralFromFin_Equation1465_rectangularSymmetry

theorem Equation3259_not_structuralFromFin_Equation162_rectangularSymmetry : ¬ Law3259.StructuralFromFin Law162 := by
  apply refutes 0
  · exact (@Law162.models_iff (Fin 16) (source 0)).mpr (by native_decide)
  · intro a b c h
    exact target3259 a b c ((@Law3259.models_iff (Fin 16) (family a b c)).mp h)

/-- info: 'Equation3259_not_structuralFromFin_Equation162_rectangularSymmetry' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3259_not_structuralFromFin_Equation162_rectangularSymmetry._native.native_decide.ax_1_1, target3259._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_2, classification._native.native_decide.ax_1_3, classification._native.native_decide.ax_1_4, classification._native.native_decide.ax_1_5, classification._native.native_decide.ax_1_6, classification._native.native_decide.ax_1_7, classification._native.native_decide.ax_1_8, classification._native.native_decide.ax_1_9, forbiddenPerm._native.native_decide.ax_1, perm._native.native_decide.ax_1, source_endos._native.native_decide.ax_1_1, source_not_endo._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3259_not_structuralFromFin_Equation162_rectangularSymmetry

theorem Equation3511_not_structuralFromFin_Equation162_rectangularSymmetry : ¬ Law3511.StructuralFromFin Law162 := by
  apply refutes 0
  · exact (@Law162.models_iff (Fin 16) (source 0)).mpr (by native_decide)
  · intro a b c h
    exact target3511 a b c ((@Law3511.models_iff (Fin 16) (family a b c)).mp h)

/-- info: 'Equation3511_not_structuralFromFin_Equation162_rectangularSymmetry' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3511_not_structuralFromFin_Equation162_rectangularSymmetry._native.native_decide.ax_1_1, target3511._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_2, classification._native.native_decide.ax_1_3, classification._native.native_decide.ax_1_4, classification._native.native_decide.ax_1_5, classification._native.native_decide.ax_1_6, classification._native.native_decide.ax_1_7, classification._native.native_decide.ax_1_8, classification._native.native_decide.ax_1_9, forbiddenPerm._native.native_decide.ax_1, perm._native.native_decide.ax_1, source_endos._native.native_decide.ax_1_1, source_not_endo._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3511_not_structuralFromFin_Equation162_rectangularSymmetry

theorem Equation3511_not_structuralFromFin_Equation837_rectangularSymmetry : ¬ Law3511.StructuralFromFin Law837 := by
  apply refutes 1
  · exact (@Law837.models_iff (Fin 16) (source 1)).mpr (by native_decide)
  · intro a b c h
    exact target3511 a b c ((@Law3511.models_iff (Fin 16) (family a b c)).mp h)

/-- info: 'Equation3511_not_structuralFromFin_Equation837_rectangularSymmetry' depends on axioms: [propext, Classical.choice, Quot.sound, Equation3511_not_structuralFromFin_Equation837_rectangularSymmetry._native.native_decide.ax_1_1, target3511._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_1, classification._native.native_decide.ax_1_2, classification._native.native_decide.ax_1_3, classification._native.native_decide.ax_1_4, classification._native.native_decide.ax_1_5, classification._native.native_decide.ax_1_6, classification._native.native_decide.ax_1_7, classification._native.native_decide.ax_1_8, classification._native.native_decide.ax_1_9, forbiddenPerm._native.native_decide.ax_1, perm._native.native_decide.ax_1, source_endos._native.native_decide.ax_1_1, source_not_endo._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3511_not_structuralFromFin_Equation837_rectangularSymmetry


