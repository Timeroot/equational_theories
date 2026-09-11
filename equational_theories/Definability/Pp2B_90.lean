import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53 (σ x) (σ y)
       grind)
    | exact superpose eq53 eq16
    | (have j1 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq53 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq72 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq72 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq65
    | exact resolve eq65 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq76 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq53 x y
       grind)
    | exact superpose eq53 eq75
    | (have j1 := eq53 x y
       grind)
    | exact resolve eq75 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq76
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq74
    | exact resolve eq74 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq90 x y
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq90
    | (have j0 := eq90 x y
       grind)
    | exact resolve eq90 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq90
  have eq1158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq1117
       have r₂ := eq75
       grind)
    | exact resolve eq1117 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1117
  have eq1163 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq1158
       have r₂ := eq16
       grind)
    | exact resolve eq1158 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1170 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq16
    | exact resolve eq16 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1191 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1170
       have i₂ := eq74 y x
       grind)
    | exact superpose eq74 eq1170
    | (have j1 := eq74 y x
       grind)
    | exact resolve eq1170 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1193 : y = (k x y) := by grind
  clear eq1191
  have eq1385 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1170
       have i₂ := eq1193
       grind)
    | exact superpose eq1193 eq1170
    | exact resolve eq1170 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1390 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1385
       have i₂ := eq53 x y
       grind)
    | exact superpose eq53 eq1385
    | (have j1 := eq53 x y
       grind)
    | exact resolve eq1385 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1391 : (M.op x y) = (k x y) := by grind
  clear eq1390
  have eq1392 : y = (M.op x y) := by
    first
    | (have i₁ := eq1391
       have i₂ := eq1193
       grind)
    | exact superpose eq1193 eq1391
    | exact resolve eq1391 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq1391
  have eq1394 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1385
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq1385
    | exact resolve eq1385 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385 eq1392
  have eq1406 : False := by grind
  exact eq1406

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq71
    | (have j1 := eq65 y x
       grind)
    | exact resolve eq71 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq95 eq65
    | (have j0 := eq65 (σ y) (σ x)
       grind)
    | exact resolve eq65 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq636
    | exact resolve eq636 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq640 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq637
       have r₂ := eq27
       grind)
    | exact resolve eq637 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq642 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq640 eq52
    | exact resolve eq52 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq644 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq640 eq14
    | exact resolve eq14 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq653 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq642 eq644
    | exact resolve eq644 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq644
  have eq659 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq653
  have eq673 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq659 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq659
       grind)
    | exact resolve eq13 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq674 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq673 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq674 eq95
    | exact resolve eq95 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq674
  have eq739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq735
  have eq743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq739
    | exact resolve eq739 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq745 : x = (M.op y x) := by
    first
    | (have r₁ := eq743
       have r₂ := eq27
       grind)
    | exact resolve eq743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq749 : x = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq745
       grind)
    | exact superpose eq745 eq14
    | exact resolve eq14 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq764 : (M.op x x) = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq14 (M.op x x) y
       have i₂ := eq749
       grind)
    | exact superpose eq749 eq14
    | exact resolve eq14 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq766 : x = (M.op x x) := by
    first
    | (have i₁ := eq764
       have i₂ := eq749
       grind)
    | exact superpose eq749 eq764
    | exact resolve eq764 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq764
  have eq774 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq766
       grind)
    | exact superpose eq766 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq766
       grind)
    | exact resolve eq13 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq774 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq804 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq776 x
       grind)
    | exact superpose eq776 eq43
    | exact resolve eq43 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq805 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq776 y
       grind)
    | exact superpose eq776 eq71
    | exact resolve eq71 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq776
  have eq810 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq805
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq805
    | exact resolve eq805 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq805
  have eq811 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq804
       have i₂ := eq766
       grind)
    | exact superpose eq766 eq804
    | exact resolve eq804 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq804
  have eq812 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq810
    | exact resolve eq810 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq810
  have eq813 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq811
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq811
    | exact resolve eq811 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq811
  have eq880 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq813 eq65
    | (have j0 := eq65 (σ x) (σ x)
       grind)
    | exact resolve eq65 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq813
  have eq881 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq880
  have eq951 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq881 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq881
       grind)
    | exact resolve eq13 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq953 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq951 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq953 eq812
    | exact resolve eq812 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq953
  have eq1043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1033
    | exact resolve eq1033 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1033
  have eq1051 : False := by grind
  exact eq1051

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq18
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq63
    | exact resolve eq63 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq76 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq66
    | exact resolve eq66 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq78 X0
       have i₂ := eq66 (M.op X0 X0)
       grind)
    | exact superpose eq66 eq78
    | exact resolve eq78 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq84 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq133 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X1
       have i₂ := eq19 (M.op X1 X1) X0
       grind)
    | exact superpose eq19 eq135
    | exact resolve eq135 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq146 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq19 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq19 eq133
    | exact resolve eq133 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq148 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 X1
       have i₂ := eq19 X1 X1
       grind)
    | exact superpose eq19 eq144
    | exact resolve eq144 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq150 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq146
    | exact resolve eq146 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq151 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq148 X1 X0
       grind)
    | exact superpose eq148 eq150
    | exact resolve eq150 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq150
  have eq152 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq136
    | exact resolve eq136 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X1 (τ X0)
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq136
    | exact resolve eq136 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq232 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 X0 X1 X2
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq206
    | (have j0 := eq206 X0 X1 X2
       grind)
    | exact resolve eq206 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq240 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232 X0 X1 X2
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq232
    | (have j0 := eq232 X0 X1 X2
       grind)
    | exact resolve eq232 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq232
  have eq304 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq151 (M.op X0 X0) X1
       have i₂ := eq136 (M.op X0 X0) X0
       grind)
    | exact superpose eq136 eq151
    | exact resolve eq151 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq306 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq151 (σ (M.op X0 X0)) X1
       have i₂ := eq152 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq152 eq151
    | exact resolve eq151 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq307 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (M.op X1 (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq151 (τ (M.op X0 X0)) X1
       have i₂ := eq178 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq178 eq151
    | exact resolve eq151 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq178
  have eq318 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq105 (M.op X0 X0)
       grind)
    | exact superpose eq105 eq307
    | exact resolve eq307 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq307
  have eq319 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq66 (M.op X0 X0)
       grind)
    | exact superpose eq66 eq306
    | exact resolve eq306 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq321 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq304
    | exact resolve eq304 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq325 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq318
    | exact resolve eq318 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq326 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq319 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq319
    | exact resolve eq319 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq332 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq321 X1 X2
       have i₂ := eq321 X1 X0
       grind)
    | (have i₁ := eq321 X0 X1
       have i₂ := eq321 X0 X0
       grind)
    | exact superpose eq321 eq321
    | exact resolve eq321 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X1
       have i₂ := eq321 X1 X0
       grind)
    | (have i₁ := eq84 X0
       have i₂ := eq321 X0 X0
       grind)
    | exact superpose eq321 eq84
    | exact resolve eq84 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq321
  have eq723 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ (M.op X0 (M.op X0 X1))) (σ X1)
       have i₂ := eq345 X0 X1
       grind)
    | exact superpose eq345 eq9
    | exact resolve eq9 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq732 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq723 X0 X1
       have i₂ := eq326 X0 (σ X0)
       grind)
    | exact superpose eq326 eq723
    | exact resolve eq723 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq1859 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq326 X1 X2
       have i₂ := eq332 X1 X1 X0
       grind)
    | (have i₁ := eq326 X1 X2
       have i₂ := eq332 X0 X1 X1
       grind)
    | exact superpose eq332 eq326
    | exact resolve eq326 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq2567 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq325 X1 X2
       have i₂ := eq332 X1 X1 X0
       grind)
    | (have i₁ := eq325 X1 X2
       have i₂ := eq332 X0 X1 X1
       grind)
    | exact superpose eq332 eq325
    | exact resolve eq325 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq332
  have eq2784 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 X0)) (τ X2)) = (τ (k (σ (M.op X0 (M.op X0 X0))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq732 X0 X1
       grind)
    | (have i₁ := eq29 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq732 X0 X1
       grind)
    | exact superpose eq732 eq29
    | exact resolve eq29 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq2800 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 X0)) (τ X2)) = (k (M.op X0 (M.op X0 X0)) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2784 X0 X1 X2
       have i₂ := eq29 (M.op X0 (M.op X0 X0)) X2
       grind)
    | exact superpose eq29 eq2784
    | exact resolve eq2784 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2784
  have eq2928 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (σ (M.op X1 (M.op X1 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1859 X1 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1859
    | exact resolve eq1859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq9570 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k (σ X0) X1) (M.op (M.op (k (σ X0) X1) (k (σ X0) X1)) (M.op (k (σ X0) X1) (k (σ X0) X1)))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X2) (k (σ X0) X1)
       have i₂ := eq240 X0 X1 X2
       grind)
    | exact superpose eq240 eq9
    | (have j1 := eq240 X0 X1 X2
       grind)
    | exact resolve eq9 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq9619 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9570 X0 X1 X2
       have i₂ := eq9 (k (σ X0) X1) (k (σ X0) X1)
       grind)
    | exact superpose eq9 eq9570
    | (have j0 := eq9570 X0 X1 X2
       grind)
    | exact resolve eq9570 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9570
  have eq263850 : ∀ X0 X1 X2 : G, (k (M.op X2 (M.op X2 X2)) X0) = (k (M.op X1 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2800 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2800
    | exact resolve eq2800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2800
  have eq264938 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) = (k (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X1 (M.op X1 X1))
       have i₂ := eq263850 (M.op X1 (M.op X1 X1)) X0 X1
       grind)
    | (have i₁ := eq54 (M.op X1 (M.op X1 x))
       have i₂ := eq263850 (M.op X1 (M.op X1 x)) X1 x
       grind)
    | exact superpose eq263850 eq54
    | exact resolve eq54 eq263850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264995 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X1 (M.op X1 X0))
       have i₂ := eq263850 (M.op X1 (M.op X1 X0)) X1 X0
       grind)
    | (have i₁ := eq54 (M.op x (M.op x x))
       have i₂ := eq263850 (M.op x (M.op x x)) X1 x
       grind)
    | exact superpose eq263850 eq54
    | exact resolve eq54 eq263850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq263850
  have eq265073 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq264995 X0 X1
       have i₂ := eq19 (M.op X1 X0) X1
       grind)
    | exact superpose eq19 eq264995
    | exact resolve eq264995 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264995
  have eq265097 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X1 X1))) = (k (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq264938 X0 X1
       have i₂ := eq19 (M.op X1 X1) X1
       grind)
    | exact superpose eq19 eq264938
    | exact resolve eq264938 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq264938
  have eq265254 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq265073 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq265073
    | exact resolve eq265073 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265073
  have eq265257 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq265097 X0 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq265097
    | exact resolve eq265097 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265097
  have eq265364 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 (M.op X0 (τ X1)))) (M.op X2 (M.op X2 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq265254 X1 X2
       have i₂ := eq2928 X1 X0 X1
       grind)
    | exact superpose eq2928 eq265254
    | exact resolve eq265254 eq2928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928 eq265254
  have eq268103 : ∀ X0 X1 X2 : G, (τ X1) = (k (M.op X2 (M.op X2 (τ X1))) (τ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq265257 X2 (τ X1)
       have i₂ := eq2567 X0 X1 (τ X1)
       grind)
    | exact superpose eq2567 eq265257
    | exact resolve eq265257 eq2567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567 eq265257
  have eq327411 : ∀ X0 X1 X2 X3 : G, (σ (k X1 (τ X0))) = (M.op (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) (σ X1)) ∨ (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) = (M.op (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0)))) ∨ (σ X1) = (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9619 (M.op X2 (M.op X2 (τ X0))) (M.op X3 (M.op X3 X0)) X1
       have i₂ := eq268103 X3 X0 X2
       grind)
    | exact superpose eq268103 eq9619
    | (have j0 := eq9619 (M.op X2 (M.op X2 (τ X0))) (M.op X3 (M.op X3 X0)) X1
       grind)
    | exact resolve eq9619 eq268103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9619 eq268103
  have eq327430 : ∀ X0 X1 X2 X3 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) = (M.op (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0)))) ∨ (σ X1) = (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq327411 X0 X1 X2 X3
       have i₂ := eq265364 X2 X0 X3
       grind)
    | exact superpose eq265364 eq327411
    | (have j0 := eq327411 X0 X1 X2 X3
       grind)
    | exact resolve eq327411 eq265364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327411
  have eq327820 : ∀ X0 X1 X2 X3 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) = (M.op (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0)))) ∨ (σ X1) = (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq327430 X0 X1 X2 X3
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq327430
    | (have j0 := eq327430 X0 X1 X2 X3
       grind)
    | exact resolve eq327430 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327430
  have eq328071 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq327820 X1 X1 X0 X2
       have i₂ := eq265364 X0 X1 X2
       grind)
    | exact superpose eq265364 eq327820
    | (have j0 := eq327820 X0 X1 X2 X3
       grind)
    | exact resolve eq327820 eq265364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327820
  have eq328248 : ∀ X0 X1 X2 X3 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (k (σ (M.op X2 (M.op X2 (τ X0)))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq328071 X0 X1 X2 X3
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq328071 X1 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq328071 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328071
  have eq328353 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq328248 X0 X1 x x
       have i₂ := eq265364 x X0 x
       grind)
    | exact superpose eq265364 eq328248
    | (have j0 := eq328248 X0 X1 x x
       grind)
    | exact resolve eq328248 eq265364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265364 eq328248
  have eq328809 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq328353 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq328353
    | exact resolve eq328353 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328871 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq328353 (σ X0) X1
       grind)
    | exact superpose eq328353 eq15
    | (have j1 := eq328353 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq328353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328353
  have eq329019 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq328809 X1 (τ X0)
       grind)
    | exact superpose eq328809 eq18
    | (have j1 := eq328809 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq328809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq328809
  have eq333663 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq329019 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq329019
    | exact resolve eq329019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329019
  have eq334274 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq333663 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq333663
    | (have j0 := eq333663 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq333663 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333663
  have eq336629 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq328871 x y
       grind)
    | exact superpose eq328871 eq16
    | (have j1 := eq328871 x y
       grind)
    | exact resolve eq16 eq328871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328871
  have eq337108 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq336629
       have i₂ := eq334274 x y
       grind)
    | exact superpose eq334274 eq336629
    | (have j1 := eq334274 (σ x) (σ y)
       grind)
    | (have r₁ := eq336629
       have r₂ := eq334274 x y
       grind)
    | (have r₁ := eq336629
       have r₂ := eq334274 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq336629
       have r₂ := eq334274 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq336629 eq334274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334274 eq336629
  have eq337111 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq337108
  have eq337623 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq337111
       grind)
    | exact superpose eq337111 eq16
    | exact resolve eq16 eq337111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337111
  have eq337624 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq337623
       have r₂ := eq66 x
       grind)
    | exact resolve eq337623 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337623
  have eq337625 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq337624
       grind)
    | exact superpose eq337624 eq16
    | exact resolve eq16 eq337624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337626 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq337624
       grind)
    | exact superpose eq337624 eq10
    | exact resolve eq10 eq337624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337624
  have eq337827 : x = y := by
    first
    | (have i₁ := eq337626
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq337626
    | exact resolve eq337626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337626
  have eq337828 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq337625
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq337625
    | exact resolve eq337625 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq337625
  have eq337850 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq337828
       have i₂ := eq337827
       grind)
    | exact superpose eq337827 eq337828
    | exact resolve eq337828 eq337827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337827 eq337828
  have eq337851 : False := by grind
  exact eq337851

/-- `Equation916`: `x = y ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pxy_x_pyx_Equation916 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law916 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law916.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq80 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq84 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq84
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq97
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq139 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq122
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq122 eq16
    | exact resolve eq16 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq139
  have eq221 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq78 X0 X0
       grind)
    | exact superpose eq78 eq14
    | (have j1 := eq78 X0 X0
       grind)
    | exact resolve eq14 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq455 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq447 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq476 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq221 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq221
    | exact resolve eq221 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2743 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq337 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq337
    | exact resolve eq337 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2748 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2743 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq2743
    | exact resolve eq2743 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743
  have eq2749 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2748 X0
       have i₂ := eq51 (M.op X0 X0)
       grind)
    | exact superpose eq51 eq2748
    | exact resolve eq2748 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq2750 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2749 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq2749
    | exact resolve eq2749 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2751 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq2750 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq2750
    | exact resolve eq2750 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2755 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq2751 X0
       have i₂ := eq2750 X0
       grind)
    | exact superpose eq2750 eq2751
    | exact resolve eq2751 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751
  have eq2783 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq338 (M.op X0 X0) X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq338
    | exact resolve eq338 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2796 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2783 X0 X1
       have i₂ := eq2750 X0
       grind)
    | exact superpose eq2750 eq2783
    | exact resolve eq2783 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq2980 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq79
    | (have j0 := eq79 x
       grind)
    | exact resolve eq79 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2984 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2980
  have eq2988 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2984
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq2984
    | exact resolve eq2984 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2984
  have eq3004 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq2988
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq2988 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988
  have eq3009 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3004 eq50
    | exact resolve eq50 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq3146 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80
    | (have j0 := eq80 y
       grind)
    | exact resolve eq80 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq3149 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3146
  have eq3152 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3149
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq3149
    | exact resolve eq3149 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149
  have eq3175 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3152
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3152 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq3196 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3175 eq102
    | exact resolve eq102 eq3175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq3363 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq123
    | (have j0 := eq123 (M.op x y)
       grind)
    | exact resolve eq123 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq3365 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3363
  have eq3367 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq122 eq3365
    | exact resolve eq3365 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq3365
  have eq3397 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3367
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3367 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367
  have eq3434 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3397 eq145
    | exact resolve eq145 eq3397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq3502 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq334 X0
       have i₂ := eq2750 X0
       grind)
    | exact superpose eq2750 eq334
    | exact resolve eq334 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq3508 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq3502 X0
       grind)
    | exact superpose eq3502 eq14
    | exact resolve eq14 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3512 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq3502 X0
       grind)
    | exact superpose eq3502 eq337
    | exact resolve eq337 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3514 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq3502 X0
       grind)
    | exact superpose eq3502 eq338
    | exact resolve eq338 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3775 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (M.op (M.op X1 X1) (k X0 (σ (τ X0))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq455 (τ X0) X1
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq455
    | (have j0 := eq455 (τ X0) X1
       grind)
    | exact resolve eq455 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq455
  have eq3785 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3775 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3775
    | (have j0 := eq3775 X0 X1
       grind)
    | exact resolve eq3775 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775
  have eq3791 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3785 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3785
    | (have j0 := eq3785 X0 X1
       grind)
    | exact resolve eq3785 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3785
  have eq8760 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3004 eq92
    | exact resolve eq92 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq8766 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3175 eq103
    | exact resolve eq103 eq3175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq10112 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3397 eq146
    | exact resolve eq146 eq3397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq3397
  have eq12066 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X1
       have i₂ := eq3508 X1 X0
       grind)
    | exact superpose eq3508 eq335
    | exact resolve eq335 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12072 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2755 X1
       have i₂ := eq3508 X1 X0
       grind)
    | exact superpose eq3508 eq2755
    | exact resolve eq2755 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12103 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12066 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq3502 X0
       grind)
    | exact superpose eq3502 eq12066
    | exact resolve eq12066 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12118 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12066 x (M.op X0 X0)
       have i₂ := eq14 X0 x
       grind)
    | exact superpose eq14 eq12066
    | exact resolve eq12066 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12543 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq8760
       grind)
    | exact superpose eq8760 eq16
    | exact resolve eq16 eq8760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8760
  have eq12601 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3009 eq12543
    | exact resolve eq12543 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12543
  have eq12606 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq12601
       have r₂ := eq13 x x
       grind)
    | exact resolve eq12601 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12601
  have eq12608 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq12606
       grind)
    | exact superpose eq12606 eq44
    | exact resolve eq44 eq12606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq12633 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq3004 eq12608
    | exact resolve eq12608 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004 eq12608
  have eq13349 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq8766
       grind)
    | exact superpose eq8766 eq16
    | exact resolve eq16 eq8766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8766
  have eq13411 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3196 eq13349
    | exact resolve eq13349 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13349
  have eq13416 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq13411
       have r₂ := eq13 y y
       grind)
    | exact resolve eq13411 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13411
  have eq13418 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq13416
       grind)
    | exact superpose eq13416 eq71
    | exact resolve eq71 eq13416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq13443 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq3175 eq13418
    | exact resolve eq13418 eq3175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3175 eq13418
  have eq14211 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10112 eq16
    | exact resolve eq16 eq10112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10112
  have eq14277 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3434 eq14211
    | exact resolve eq14211 eq3434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14211
  have eq14282 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq14277
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq14277 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14277
  have eq16465 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq12103
    | (have j0 := eq12103 (σ x) (σ y)
       grind)
    | exact resolve eq12103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq20241
    | exact resolve eq20241 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20241
  have eq20253 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq20242
       have r₂ := eq28
       grind)
    | exact resolve eq20242 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20242
  have eq20259 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20253 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20253
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20253
       grind)
    | exact resolve eq13 eq20253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20260 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq20259
  have eq20268 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20260 eq96
    | exact resolve eq96 eq20260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq20260
  have eq20278 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20268
  have eq20618 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20278 eq3196
    | exact resolve eq3196 eq20278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20278
  have eq20675 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20618
       have i₂ := eq13416
       grind)
    | exact superpose eq13416 eq20618
    | exact resolve eq20618 eq13416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20618
  have eq20684 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq20675
    | exact resolve eq20675 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20675
  have eq20685 : y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20684
  have eq20690 : x = (M.op x (M.op (M.op y (M.op y y)) y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12103 y x
       have i₂ := eq20685
       grind)
    | exact superpose eq20685 eq12103
    | exact resolve eq12103 eq20685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20685
  have eq20693 : x = (M.op x (M.op y y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20690
       have i₂ := eq2755 y
       grind)
    | exact superpose eq2755 eq20690
    | exact resolve eq20690 eq2755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20690
  have eq21106 : y = (M.op (M.op x (M.op x x)) x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2796 x y
       have i₂ := eq20693
       grind)
    | exact superpose eq20693 eq2796
    | exact resolve eq2796 eq20693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20693
  have eq21113 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq21106
       have i₂ := eq2755 x
       grind)
    | exact superpose eq2755 eq21106
    | exact resolve eq21106 eq2755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21106
  have eq21120 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12633
       have i₂ := eq21113
       grind)
    | exact superpose eq21113 eq12633
    | exact resolve eq12633 eq21113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12633
  have eq21128 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq21113
       grind)
    | exact superpose eq21113 eq51
    | exact resolve eq51 eq21113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21113
  have eq21175 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq21128
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21128
    | exact resolve eq21128 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21128
  have eq21182 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq21120
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21120
    | exact resolve eq21120 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21120
  have eq21756 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13443
       have i₂ := eq21175
       grind)
    | exact superpose eq21175 eq13443
    | exact resolve eq13443 eq21175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21175
  have eq21804 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq21756
    | exact resolve eq21756 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21756
  have eq22193 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21182 eq51
    | exact resolve eq51 eq21182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21182
  have eq22240 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq22193
    | exact resolve eq22193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22193
  have eq22722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22240 eq21804
    | exact resolve eq21804 eq22240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21804 eq22240
  have eq22758 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22722
  have eq22767 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq22758
       have r₂ := eq28
       grind)
    | exact resolve eq22758 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22758
  have eq22787 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13443
       have i₂ := eq22767
       grind)
    | exact superpose eq22767 eq13443
    | exact resolve eq13443 eq22767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22791 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 X0) x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq22767
       grind)
    | exact superpose eq22767 eq14
    | exact resolve eq14 eq22767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22793 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq22767
       grind)
    | exact superpose eq22767 eq51
    | exact resolve eq51 eq22767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22805 : ∀ X0 : G, y = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2796 X0 y
       have i₂ := eq22767
       grind)
    | exact superpose eq22767 eq2796
    | exact resolve eq2796 eq22767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22818 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12118 y
       have i₂ := eq22767
       grind)
    | exact superpose eq22767 eq12118
    | exact resolve eq12118 eq22767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22767
  have eq22826 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22818
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22818
    | exact resolve eq22818 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22818
  have eq22829 : y = (M.op x (M.op x x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq22791 x
       have i₂ := eq3508 x x
       grind)
    | exact superpose eq3508 eq22791
    | exact resolve eq22791 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22791
  have eq22832 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq22787
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22787
    | exact resolve eq22787 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22787
  have eq22842 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22826 eq30
    | exact resolve eq30 eq22826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22826
  have eq22974 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq22842
    | exact resolve eq22842 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22842
  have eq23129 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq22974
  have eq23368 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22832 eq12118
    | exact resolve eq12118 eq22832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23379 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq23368
    | exact resolve eq23368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23368
  have eq23404 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23379 eq28
    | exact resolve eq28 eq23379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23379
  have eq23837 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op (M.op X0 X0) y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq337 x X0
       have i₂ := eq22829
       grind)
    | exact superpose eq22829 eq337
    | exact resolve eq337 eq22829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23855 : (M.op x x) = (M.op y (M.op y y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq23837 x
       have i₂ := eq3508 y x
       grind)
    | exact superpose eq3508 eq23837
    | exact resolve eq23837 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23837
  have eq78909 : y = (M.op (M.op x x) (M.op y x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq22805 y
       have i₂ := eq23855
       grind)
    | exact superpose eq23855 eq22805
    | exact resolve eq22805 eq23855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22805 eq23855
  have eq78939 : y = (M.op (M.op x x) (M.op y x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq78909
  have eq78999 : (M.op y x) = (M.op (M.op y x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12066 x (M.op y x)
       have i₂ := eq78939
       grind)
    | exact superpose eq78939 eq12066
    | exact resolve eq12066 eq78939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78939
  have eq79009 : (M.op y x) = (M.op (M.op y x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq78999
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq78999
    | exact resolve eq78999 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78999
  have eq79033 : (M.op x x) = (M.op (M.op x x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq79009
       have i₂ := eq22793
       grind)
    | exact superpose eq22793 eq79009
    | exact resolve eq79009 eq22793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22793 eq79009
  have eq79041 : (M.op x x) = (M.op (M.op x x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq79033
  have eq80707 : (M.op x y) = (M.op (M.op x y) (M.op x (M.op x x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq79041 eq12066
    | exact resolve eq12066 eq79041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12066 eq79041
  have eq82207 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq80707
       have i₂ := eq22829
       grind)
    | exact superpose eq22829 eq80707
    | exact resolve eq80707 eq22829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22829 eq80707
  have eq82213 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq82207
  have eq82221 : y = (M.op y (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq82213 eq12103
    | exact resolve eq12103 eq82213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82213
  have eq82224 : y = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq82221
       have i₂ := eq2755 sF0
       grind)
    | exact superpose eq2755 eq82221
    | exact resolve eq82221 eq2755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82221
  have eq82331 : (M.op x y) = (M.op (M.op y (M.op y y)) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq82224 eq2796
    | exact resolve eq2796 eq82224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82224
  have eq82340 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq82331
       have i₂ := eq2755 y
       grind)
    | exact superpose eq2755 eq82331
    | exact resolve eq82331 eq2755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82331
  have eq82349 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13443
       have i₂ := eq82340
       grind)
    | exact superpose eq82340 eq13443
    | exact resolve eq13443 eq82340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13443 eq82340
  have eq82465 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq82349
    | exact resolve eq82349 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq82349
  have eq82494 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq82465 eq22832
    | exact resolve eq22832 eq82465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22832 eq82465
  have eq82578 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq82494
  have eq82592 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq82578
       have r₂ := eq23404
       grind)
    | exact resolve eq82578 eq23404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23404 eq82578
  have eq82618 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq82592 eq27
    | exact resolve eq27 eq82592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq82619 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq82592 eq30
    | exact resolve eq30 eq82592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq82686 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq82592 eq16465
    | exact resolve eq16465 eq82592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16465
  have eq82817 : y = (M.op x y) := by
    first
    | exact superpose eq31 eq82619
    | exact resolve eq82619 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq82619
  have eq94374 : (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ (M.op x y)))) := by
    first
    | exact superpose eq82686 eq12103
    | exact resolve eq12103 eq82686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82686
  have eq94377 : (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq94374
       have i₂ := eq2755 sF1
       grind)
    | exact superpose eq2755 eq94374
    | exact resolve eq94374 eq2755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94374
  have eq593123 : (σ (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))))) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq94377 eq2796
    | exact resolve eq2796 eq94377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94377
  have eq593133 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq593123
       have i₂ := eq2755 (M.op (M.op sF2 (M.op sF2 sF2)) sF4)
       grind)
    | exact superpose eq2755 eq593123
    | exact resolve eq593123 eq2755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593123
  have eq593144 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) = (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq593133 eq338
    | exact resolve eq338 eq593133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593167 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq593133 eq3508
    | exact resolve eq3508 eq593133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593133
  have eq593242 : (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq593144 x
       have i₂ := eq3514 sF1 x
       grind)
    | exact superpose eq3514 eq593144
    | exact resolve eq593144 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593144
  have eq596642 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq593242 eq593167
    | exact resolve eq593167 eq593242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593167 eq593242
  have eq596663 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq596642 X1
       have i₂ := eq3508 X1 X0
       grind)
    | exact superpose eq3508 eq596642
    | exact resolve eq596642 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596688 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ (M.op x y)) X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2796 X0 X1
       have i₂ := eq596642 X0
       grind)
    | exact superpose eq596642 eq2796
    | exact resolve eq2796 eq596642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596706 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ (M.op x y)) X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12103 X0 X1
       have i₂ := eq596642 X0
       grind)
    | exact superpose eq596642 eq12103
    | exact resolve eq12103 eq596642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12103 eq596642
  have eq604000 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq596663 eq596663
    | exact resolve eq596663 eq596663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604539 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X2) X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq604000 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq3502 X0
       grind)
    | exact superpose eq3502 eq604000
    | exact resolve eq604000 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604000
  have eq605241 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X1 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq596663 eq596688
    | exact resolve eq596688 eq596663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596663 eq596688
  have eq605544 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op (M.op X1 X1) X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq605241 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq3502 X0
       grind)
    | exact superpose eq3502 eq605241
    | exact resolve eq605241 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605241
  have eq605781 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq596706 (M.op X1 (M.op X1 X1)) X1
       have i₂ := eq3512 sF1 X1
       grind)
    | exact superpose eq3512 eq596706
    | exact resolve eq596706 eq3512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605827 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ (M.op x y)) (M.op X1 (M.op X1 X1)))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq596706 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0))
       have i₂ := eq2796 X1 X0
       grind)
    | exact superpose eq2796 eq596706
    | exact resolve eq596706 eq2796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2796 eq596706
  have eq606246 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq605827 X0 X1
       have i₂ := eq3512 sF1 X1
       grind)
    | exact superpose eq3512 eq605827
    | exact resolve eq605827 eq3512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605827
  have eq607130 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) X0) = (M.op (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) X0) (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq605781 X1 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) X0)
       have i₂ := eq3508 X0 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq3508 eq605781
    | exact resolve eq605781 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605781
  have eq607334 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq607130 X0 X0
       have i₂ := eq3502 X0
       grind)
    | exact superpose eq3502 eq607130
    | exact resolve eq607130 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3502 eq607130
  have eq636122 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq604539 X1 X0 X0
       have i₂ := eq12118 X0
       grind)
    | exact superpose eq12118 eq604539
    | exact resolve eq604539 eq12118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636432 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) y)) = (M.op (M.op x (M.op x x)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq604539 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq604539
    | (have j0 := eq604539 x y X0
       grind)
    | exact resolve eq604539 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604539
  have eq637070 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) y)) = (M.op (M.op x (M.op x x)) y) := by
    intro X0
    first
    | exact superpose eq82817 eq636432
    | exact resolve eq636432 eq82817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636432
  have eq637309 : (M.op y (M.op y y)) = (M.op (M.op x (M.op x x)) y) := by
    first
    | (have i₁ := eq637070 x
       have i₂ := eq3508 y x
       grind)
    | exact superpose eq3508 eq637070
    | exact resolve eq637070 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3508 eq637070
  have eq637431 : (M.op y (M.op y y)) = (M.op (M.op x x) (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq3514 y x
       have i₂ := eq637309
       grind)
    | exact superpose eq637309 eq3514
    | exact resolve eq3514 eq637309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514 eq637309
  have eq652854 : (M.op y y) = (M.op x (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq337 y x
       have i₂ := eq637431
       grind)
    | exact superpose eq637431 eq337
    | exact resolve eq337 eq637431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637431
  have eq654780 : (M.op y y) = (M.op (M.op x (M.op x x)) (M.op y y)) := by
    first
    | (have i₁ := eq3512 x y
       have i₂ := eq652854
       grind)
    | exact superpose eq652854 eq3512
    | exact resolve eq3512 eq652854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3512
  have eq654813 : y = (M.op (M.op x x) (M.op y y)) := by
    first
    | (have i₁ := eq338 x y
       have i₂ := eq654780
       grind)
    | exact superpose eq654780 eq338
    | exact resolve eq338 eq654780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq654780
  have eq671593 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2750 X2
       have i₂ := eq605544 X2 X0 X1
       grind)
    | exact superpose eq605544 eq2750
    | exact resolve eq2750 eq605544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750 eq605544
  have eq743419 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq607334 (M.op (M.op X1 X1) X0) (M.op X1 (M.op X0 X0))
       have i₂ := eq606246 X0 X1
       grind)
    | exact superpose eq606246 eq607334
    | exact resolve eq607334 eq606246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606246 eq607334
  have eq743996 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq743419 X0 X1
       have i₂ := eq337 (M.op (M.op X0 X0) X1) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq337 eq743419
    | exact resolve eq743419 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq743419
  have eq805447 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (k X0 X0)) (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq743996 X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (k X0 X0))
       have i₂ := eq3791 X0 (M.op X0 X0)
       grind)
    | exact superpose eq3791 eq743996
    | (have j1 := eq3791 X0 X1
       grind)
    | exact resolve eq743996 eq3791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq805858 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op (k X0 X0) (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq805447 X0 X1
       have i₂ := eq743996 (M.op X1 X1) (k X0 X0)
       grind)
    | exact superpose eq743996 eq805447
    | (have j0 := eq805447 X0 X1
       grind)
    | exact resolve eq805447 eq743996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743996 eq805447
  have eq805966 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq805858 X0 x
       have i₂ := eq14 (k X0 X0) x
       grind)
    | exact superpose eq14 eq805858
    | (have j0 := eq805858 X0 x
       grind)
    | exact resolve eq805858 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805858
  have eq806017 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq805966 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq805966 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq805966 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805966
  have eq806430 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq476 X0 X0
       have i₂ := eq806017 (τ X0)
       grind)
    | exact superpose eq806017 eq476
    | exact resolve eq476 eq806017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq806836 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq806430 X0
       have i₂ := eq806017 X0
       grind)
    | exact superpose eq806017 eq806430
    | exact resolve eq806430 eq806017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806017 eq806430
  have eq808358 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12118 (τ X0)
       have i₂ := eq806836 X0
       grind)
    | exact superpose eq806836 eq12118
    | exact resolve eq12118 eq806836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816209 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (M.op X1 (M.op (M.op X1 X1) (τ (M.op X0 X0)))) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq671593 X1 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq808358 X0
       grind)
    | exact superpose eq808358 eq671593
    | exact resolve eq671593 eq808358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808358
  have eq816221 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq816209 X0 x
       have i₂ := eq12072 x (τ (M.op X0 X0))
       grind)
    | exact superpose eq12072 eq816209
    | exact resolve eq816209 eq12072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816209
  have eq816387 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq816221 X0
       have i₂ := eq806836 (M.op X0 X0)
       grind)
    | exact superpose eq806836 eq816221
    | exact resolve eq816221 eq806836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816221
  have eq816503 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq816387 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq816387
    | exact resolve eq816387 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq816387
  have eq816578 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq816503 X0
       have i₂ := eq806836 X0
       grind)
    | exact superpose eq806836 eq816503
    | exact resolve eq816503 eq806836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806836 eq816503
  have eq871272 : ∀ X0 X1 : G, (τ X1) = (M.op (τ (M.op X1 X1)) (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq816578 X1
       have i₂ := eq636122 X1 X0
       grind)
    | exact superpose eq636122 eq816578
    | exact resolve eq816578 eq636122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636122 eq816578
  have eq2474163 : (τ (σ x)) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20253 eq871272
    | exact resolve eq871272 eq20253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20253 eq871272
  have eq2474671 : (τ (σ x)) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2474163
       have i₂ := eq2755 sF3
       grind)
    | exact superpose eq2755 eq2474163
    | exact resolve eq2474163 eq2755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755 eq2474163
  have eq2475403 : (τ (σ x)) = (M.op (τ (M.op (σ x) (σ x))) (k y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3196 eq2474671
    | exact resolve eq2474671 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196 eq2474671
  have eq2475976 : (τ (σ x)) = (M.op (τ (M.op (σ x) (σ x))) (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2475403
       have i₂ := eq13416
       grind)
    | exact superpose eq13416 eq2475403
    | exact resolve eq2475403 eq13416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13416 eq2475403
  have eq2476384 : (τ (σ x)) = (M.op (k x x) (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3009 eq2475976
    | exact resolve eq2475976 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009 eq2475976
  have eq2476651 : (τ (σ x)) = (M.op (M.op x x) (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2476384
       have i₂ := eq12606
       grind)
    | exact superpose eq12606 eq2476384
    | exact resolve eq2476384 eq12606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12606 eq2476384
  have eq2476837 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2476651
       have i₂ := eq654813
       grind)
    | exact superpose eq654813 eq2476651
    | exact resolve eq2476651 eq654813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2476651
  have eq2476955 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq2476837
    | exact resolve eq2476837 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2476837
  have eq2477028 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq82592 eq2476955
    | exact resolve eq2476955 eq82592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2476955
  have eq2809516 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2477028 eq3434
    | exact resolve eq3434 eq2477028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477028
  have eq2810769 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14282 eq2809516
    | exact resolve eq2809516 eq14282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2809516
  have eq2810988 : (τ (σ x)) = (M.op y y) ∨ x = y ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq82817 eq2810769
    | exact resolve eq2810769 eq82817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810769
  have eq2811171 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq2810988
    | exact resolve eq2810988 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2810988
  have eq2811172 : y = (M.op y x) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2811171
  have eq2811341 : ∀ X0 : G, x = (M.op (M.op x x) (M.op (M.op X0 (M.op (M.op X0 X0) y)) y)) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq671593 X0 y x
       have i₂ := eq2811172
       grind)
    | exact superpose eq2811172 eq671593
    | exact resolve eq671593 eq2811172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671593 eq2811172
  have eq2811417 : x = (M.op (M.op x x) (M.op y y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2811341 x
       have i₂ := eq12072 x y
       grind)
    | exact superpose eq12072 eq2811341
    | exact resolve eq2811341 eq12072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12072 eq2811341
  have eq2811451 : x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2811417
       have i₂ := eq654813
       grind)
    | exact superpose eq654813 eq2811417
    | exact resolve eq2811417 eq654813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654813 eq2811417
  have eq2811452 : x = (M.op y y) ∨ x = y := by grind
  clear eq2811451
  have eq2811697 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12118 y
       have i₂ := eq2811452
       grind)
    | exact superpose eq2811452 eq12118
    | exact resolve eq12118 eq2811452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12118 eq2811452
  have eq2812700 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2811697
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2811697
    | exact resolve eq2811697 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2811697
  have eq2813035 : x = (M.op x y) := by
    first
    | (have r₁ := eq2812700
       have r₂ := eq23129
       grind)
    | exact resolve eq2812700 eq23129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23129 eq2812700
  have eq2813290 : x = y := by
    first
    | exact superpose eq82817 eq2813035
    | exact resolve eq2813035 eq82817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2813035
  have eq2813558 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2813290
       grind)
    | exact superpose eq2813290 eq25
    | exact resolve eq25 eq2813290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq2814279 : (M.op x x) = (M.op x (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq652854
       have i₂ := eq2813290
       grind)
    | exact superpose eq2813290 eq652854
    | exact resolve eq652854 eq2813290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652854
  have eq2814327 : x = (M.op x x) := by
    first
    | (have i₁ := eq2814279
       have i₂ := eq335 x
       grind)
    | exact superpose eq335 eq2814279
    | exact resolve eq2814279 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq2814279
  have eq2814894 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq82592 eq2813558
    | exact resolve eq2813558 eq82592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82592 eq2813558
  have eq2815372 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2814894
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2814894
    | exact resolve eq2814894 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2814894
  have eq2816178 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2815372 eq82618
    | exact resolve eq82618 eq2815372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82618
  have eq2819045 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2816178 eq3434
    | exact resolve eq3434 eq2816178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3434 eq2816178
  have eq2820324 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq14282 eq2819045
    | exact resolve eq2819045 eq14282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14282 eq2819045
  have eq2820662 : (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq82817 eq2820324
    | exact resolve eq2820324 eq82817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82817 eq2820324
  have eq2820893 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2820662
       have i₂ := eq2813290
       grind)
    | exact superpose eq2813290 eq2820662
    | exact resolve eq2820662 eq2813290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2813290 eq2820662
  have eq2820961 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2820893
       have i₂ := eq2814327
       grind)
    | exact superpose eq2814327 eq2820893
    | exact resolve eq2820893 eq2814327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2814327 eq2820893
  have eq2821096 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2820961 eq15
    | exact resolve eq15 eq2820961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820961
  have eq2822947 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2821096
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2821096
    | exact resolve eq2821096 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2821096
  have eq2823583 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2815372 eq2822947
    | exact resolve eq2822947 eq2815372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815372 eq2822947
  have eq2824173 : False := by grind
  exact eq2824173

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyy_pyy_pyx_Equation947 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k (M.op (M.op X2 X0) (M.op X1 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 (M.op (M.op X2 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq124
    | (have j0 := eq124 (M.op (M.op X2 X0) (M.op X1 X0)) X1
       grind)
    | (have r₁ := eq124 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq124 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X1 X0) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq428 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X0 X2 X2 X1
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq428 X1 x X0
       grind)
    | exact superpose eq428 eq9
    | exact resolve eq9 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq306 X0 x
       have i₂ := eq428 X0 x X0
       grind)
    | exact superpose eq428 eq306
    | exact resolve eq306 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq441 X2 (M.op X0 X1)
       have i₂ := eq428 X1 X0 X0
       grind)
    | exact superpose eq428 eq441
    | exact resolve eq441 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq441 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq441 (M.op X0 X0) X0
       grind)
    | exact superpose eq441 eq441
    | exact resolve eq441 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq441 (M.op X1 X0) X0
       have i₂ := eq428 X0 X1 X0
       grind)
    | exact superpose eq428 eq441
    | exact resolve eq441 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 X1 X0 X0
       have i₂ := eq441 X1 (M.op X0 X1)
       grind)
    | exact superpose eq441 eq51
    | exact resolve eq51 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq441 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq441 eq9
    | exact resolve eq9 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq481 X0 X1
       have i₂ := eq428 X1 X0 X0
       grind)
    | exact superpose eq428 eq481
    | exact resolve eq481 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq540 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq442 (M.op X0 X0)
       have i₂ := eq441 (M.op X0 X0) X0
       grind)
    | exact superpose eq441 eq442
    | exact resolve eq442 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq554 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq540 X0
       have i₂ := eq428 X0 X0 X0
       grind)
    | exact superpose eq428 eq540
    | exact resolve eq540 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq569 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq306 (M.op X0 (M.op X0 X0)) (M.op x X0)
       have i₂ := eq479 X0 x
       grind)
    | exact superpose eq479 eq306
    | exact resolve eq306 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq574 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq569 X0
       have i₂ := eq9 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq9 eq569
    | exact resolve eq569 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq585 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq574 X0
       have i₂ := eq428 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq428 eq574
    | exact resolve eq574 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq591 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq585 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq585
    | exact resolve eq585 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq596 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 (M.op X1 (M.op X0 X0))) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 X2 X1
       have i₂ := eq428 X0 X1 X2
       grind)
    | exact superpose eq428 eq52
    | exact resolve eq52 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq635 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq499 (M.op X1 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq479 X0 X1
       grind)
    | exact superpose eq479 eq499
    | exact resolve eq499 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq499 X1 X0
       grind)
    | (have i₁ := eq493 X1 X1
       have i₂ := eq499 X1 X1
       grind)
    | exact superpose eq499 eq493
    | exact resolve eq493 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq441 X1 X0
       have i₂ := eq499 X1 X0
       grind)
    | (have i₁ := eq441 X1 X1
       have i₂ := eq499 X1 X1
       grind)
    | exact superpose eq499 eq441
    | exact resolve eq441 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq479 (M.op X0 X1) X1
       have i₂ := eq499 X0 X1
       grind)
    | (have i₁ := eq479 (M.op X1 X1) X0
       have i₂ := eq499 X0 X1
       grind)
    | exact superpose eq499 eq479
    | exact resolve eq479 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq678 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1
       have i₂ := eq428 X1 X0 X0
       grind)
    | exact superpose eq428 eq676
    | exact resolve eq676 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq702 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq635 X0 X1
       have i₂ := eq428 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq428 eq635
    | exact resolve eq635 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq709 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq678 X0 X1
       have i₂ := eq499 (M.op X0 X1) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq499 eq678
    | exact resolve eq678 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq723 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq702
    | exact resolve eq702 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq727 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq709 X0 X1
       have i₂ := eq428 (M.op X1 X1) X0 X0
       grind)
    | exact superpose eq428 eq709
    | exact resolve eq709 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq732 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq723 X0 X1
       have i₂ := eq493 X0 X0
       grind)
    | exact superpose eq493 eq723
    | exact resolve eq723 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq723
  have eq734 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq499 (M.op X1 X1) X1
       grind)
    | exact superpose eq499 eq727
    | exact resolve eq727 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq737 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq478 X1
       grind)
    | exact superpose eq478 eq734
    | exact resolve eq734 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1001 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq642 X0 (M.op X0 (M.op X1 X0))
       have i₂ := eq641 X0 X1
       grind)
    | exact superpose eq641 eq642
    | exact resolve eq642 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq1064 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq210 y x
       grind)
    | exact superpose eq210 eq16
    | (have j1 := eq210 y x
       grind)
    | exact resolve eq16 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = (M.op X1 (M.op (M.op X2 (M.op X1 (σ (k X0 X0)))) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq596 (σ X0) X1 X2
       have i₂ := eq210 X0 X0
       grind)
    | exact superpose eq210 eq596
    | (have j1 := eq210 X0 X0
       grind)
    | exact resolve eq596 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq596
  have eq1093 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = (M.op X1 (M.op (M.op X2 (M.op X1 (σ (k X0 X0)))) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1089 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1124 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq477 X1 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq477
    | exact resolve eq477 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op X2 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq477 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq477 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq477 eq477
    | exact resolve eq477 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1132 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq477 X1 (M.op (M.op X0 X1) (M.op X2 X1)) (M.op (M.op X0 X1) (M.op X2 X1))
       have i₂ := eq51 X1 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X0
       grind)
    | exact superpose eq51 eq477
    | exact resolve eq477 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1206 : ∀ X1 X2 : G, (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X1 X1))) = (M.op X1 (M.op X2 (M.op X1 X1))) := by
    intro X1 X2
    first
    | (have i₁ := eq1132 X1 x X2
       have i₂ := eq428 x X1 X2
       grind)
    | exact superpose eq428 eq1132
    | exact resolve eq1132 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1211 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X2 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1126 X0 X1 X2
       have i₂ := eq428 (M.op X1 X1) X0 X0
       grind)
    | exact superpose eq428 eq1126
    | exact resolve eq1126 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1235 : ∀ X1 X2 : G, (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X1 (M.op X2 (M.op X1 X1))) := by
    intro X1 X2
    first
    | (have i₁ := eq1206 X1 X2
       have i₂ := eq428 (M.op X1 X1) X2 X2
       grind)
    | exact superpose eq428 eq1206
    | exact resolve eq1206 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1237 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = (M.op X2 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1211 X0 X1 X2
       have i₂ := eq499 (M.op X1 X1) X1
       grind)
    | exact superpose eq499 eq1211
    | exact resolve eq1211 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1251 : ∀ X1 X2 : G, (M.op X2 (M.op X1 (M.op (M.op X1 X1) X1))) = (M.op X1 (M.op X2 (M.op X1 X1))) := by
    intro X1 X2
    first
    | (have i₁ := eq1235 X1 X2
       have i₂ := eq499 (M.op X1 X1) X1
       grind)
    | exact superpose eq499 eq1235
    | exact resolve eq1235 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1253 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = (M.op X2 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1237 X0 X1 X2
       have i₂ := eq732 X1 X1
       grind)
    | exact superpose eq732 eq1237
    | exact resolve eq1237 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1260 : ∀ X1 X2 : G, (M.op X2 (M.op X1 (M.op X1 X1))) = (M.op X1 (M.op X2 (M.op X1 X1))) := by
    intro X1 X2
    first
    | (have i₁ := eq1251 X1 X2
       have i₂ := eq732 X1 X1
       grind)
    | exact superpose eq732 eq1251
    | exact resolve eq1251 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1311 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq591 X1
       have i₂ := eq1124 X1 X1 X0
       grind)
    | (have i₁ := eq591 X1
       have i₂ := eq1124 X1 X0 X1
       grind)
    | exact superpose eq1124 eq591
    | exact resolve eq591 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq1315 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq642 X1 X1
       have i₂ := eq1124 X1 X1 X0
       grind)
    | (have i₁ := eq642 X1 X1
       have i₂ := eq1124 X1 X0 X1
       grind)
    | exact superpose eq1124 eq642
    | exact resolve eq642 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq1316 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq477 X1 X1 X2
       have i₂ := eq1124 X1 X1 X0
       grind)
    | (have i₁ := eq477 X1 X1 X2
       have i₂ := eq1124 X1 X0 X1
       grind)
    | exact superpose eq1124 eq477
    | exact resolve eq477 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq1371 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X0 X1))) = (M.op X3 (M.op (M.op X3 X1) (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq428 (M.op X3 X1) X2 X3
       have i₂ := eq1124 X1 X3 X0
       grind)
    | (have i₁ := eq428 (M.op X3 X1) X2 X3
       have i₂ := eq1124 X1 X0 X3
       grind)
    | exact superpose eq1124 eq428
    | exact resolve eq428 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1387 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1371 X0 X1 X2 X3
       have i₂ := eq9 X1 X3 X3
       grind)
    | exact superpose eq9 eq1371
    | exact resolve eq1371 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1628 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1311 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq1315 X1 X0
       grind)
    | exact superpose eq1315 eq1311
    | exact resolve eq1311 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311 eq1315
  have eq1650 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1628 X0 X1
       have i₂ := eq428 (M.op X1 X0) X1 X1
       grind)
    | exact superpose eq428 eq1628
    | exact resolve eq1628 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1674 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1650 X0 X1
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq1650
    | exact resolve eq1650 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq3939 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1316 X1 X2 X1
       have i₂ := eq1124 (M.op X1 X2) X1 X0
       grind)
    | (have i₁ := eq1316 X1 X2 X1
       have i₂ := eq1124 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq1124 eq1316
    | exact resolve eq1316 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6194 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1064
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1064
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq1064 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq6195 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq6194
  have eq6287 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3939 X1 X0 X1
       have i₂ := eq499 X0 X1
       grind)
    | (have i₁ := eq3939 X0 X1 X1
       have i₂ := eq499 X0 X1
       grind)
    | exact superpose eq499 eq3939
    | exact resolve eq3939 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq6807 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k (τ X0) (τ X0)))) = (M.op X1 (M.op (M.op X2 (M.op X1 (σ (k (τ X0) (τ X0))))) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1093 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1093
    | exact resolve eq1093 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq6894 : ∀ X0 X1 X2 : G, (M.op X1 (k X0 (σ (τ X0)))) = (M.op X1 (M.op (M.op X2 (M.op X1 (k X0 (σ (τ X0))))) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6807 X0 X1 X2
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq6807
    | (have j0 := eq6807 X0 X1 X2
       grind)
    | exact resolve eq6807 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq6807
  have eq6928 : ∀ X0 X1 X2 : G, (M.op X1 (k X0 X0)) = (M.op X1 (M.op (M.op X2 (M.op X1 (k X0 X0))) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6894 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6894
    | (have j0 := eq6894 X0 X1 X2
       grind)
    | exact resolve eq6894 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6894
  have eq7280 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6287 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq1387 X0 X1 X0 X0
       grind)
    | exact superpose eq1387 eq6287
    | exact resolve eq6287 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387 eq6287
  have eq9598 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq737 X2 X1
       have i₂ := eq1124 X1 X1 X0
       grind)
    | (have i₁ := eq737 X2 X1
       have i₂ := eq1124 X1 X0 X1
       grind)
    | exact superpose eq1124 eq737
    | exact resolve eq737 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq10711 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 (M.op X1 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1253 X2 X1 X2
       have i₂ := eq1124 X1 X2 X0
       grind)
    | (have i₁ := eq1253 X2 X1 X2
       have i₂ := eq1124 X1 X0 X2
       grind)
    | exact superpose eq1124 eq1253
    | exact resolve eq1253 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124 eq1253
  have eq96284 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 (k X1 X1))) (M.op X0 (M.op X0 (k X1 X1)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3939 X0 (M.op X2 (M.op X0 (k X1 X1))) X1
       have i₂ := eq6928 X1 X0 X2
       grind)
    | exact superpose eq6928 eq3939
    | (have j1 := eq6928 X1 X1 X2
       grind)
    | exact resolve eq3939 eq6928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3939 eq6928
  have eq96629 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X0 (k X1 X1)) (M.op X0 (k X1 X1)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96284 X0 X1 x
       have i₂ := eq428 (M.op X0 (k X1 X1)) x X0
       grind)
    | exact superpose eq428 eq96284
    | (have j0 := eq96284 X0 X1 x
       grind)
    | exact resolve eq96284 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq96284
  have eq96798 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq96629 x X1
       have i₂ := eq9 (k X1 X1) x x
       grind)
    | exact superpose eq9 eq96629
    | (have j0 := eq96629 x X1
       grind)
    | exact resolve eq96629 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96629
  have eq96888 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    first
    | (have j0 := eq96798 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq96798 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq96798 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96798
  have eq96978 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq96888 (σ X0)
       grind)
    | exact superpose eq96888 eq15
    | exact resolve eq15 eq96888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97015 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96978 X0
       have i₂ := eq96888 X0
       grind)
    | exact superpose eq96888 eq96978
    | exact resolve eq96978 eq96888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96888 eq96978
  have eq97379 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X1 (σ X0)
       have i₂ := eq97015 X0
       grind)
    | exact superpose eq97015 eq441
    | exact resolve eq441 eq97015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq97387 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq478 (σ X0)
       have i₂ := eq97015 X0
       grind)
    | exact superpose eq97015 eq478
    | exact resolve eq478 eq97015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq97412 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1674 (σ X0) X1
       have i₂ := eq97015 X0
       grind)
    | exact superpose eq97015 eq1674
    | exact resolve eq1674 eq97015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97495 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1674 (σ X0) (σ X0)
       have i₂ := eq97015 X0
       grind)
    | exact superpose eq97015 eq1674
    | exact resolve eq1674 eq97015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq97576 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq97495 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq97495
    | exact resolve eq97495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97495
  have eq97590 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97412 X0 X1
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq97412
    | exact resolve eq97412 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97412
  have eq97612 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq97576 X0
       have i₂ := eq554 X0
       grind)
    | exact superpose eq554 eq97576
    | exact resolve eq97576 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97576
  have eq97622 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97590 X0 X1
       have i₂ := eq554 X0
       grind)
    | exact superpose eq554 eq97590
    | exact resolve eq97590 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq97590
  have eq113297 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X1 (σ (M.op X2 (M.op X2 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97622 (M.op X2 (M.op X2 X0)) X1
       have i₂ := eq1316 X2 X0 (M.op X2 (M.op X2 X0))
       grind)
    | exact superpose eq1316 eq97622
    | exact resolve eq97622 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97622
  have eq120373 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq124 (σ x) (σ y)
       have i₂ := eq6195
       grind)
    | exact superpose eq6195 eq124
    | (have j0 := eq124 (σ x) (σ y)
       grind)
    | (have r₁ := eq124 (σ x) (σ y)
       have r₂ := eq6195
       grind)
    | (have r₁ := eq124 (σ y) (σ x)
       have r₂ := eq6195
       grind)
    | (have r₁ := eq124 y x
       have r₂ := eq6195
       grind)
    | exact resolve eq124 eq6195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6195
  have eq120484 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq120373
  have eq120578 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq120484
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq120484
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq120484
       have r₂ := eq12 y x
       grind)
    | exact resolve eq120484 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120484
  have eq120624 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq120578
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq120578
    | exact resolve eq120578 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120578
  have eq120642 : (σ (k x y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq120624
       have i₂ := eq97015 y
       grind)
    | exact superpose eq97015 eq120624
    | exact resolve eq120624 eq97015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120624
  have eq1686647 : (k x y) = (τ (σ (M.op y y))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq120642
       grind)
    | exact superpose eq120642 eq10
    | exact resolve eq10 eq120642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120642
  have eq1687069 : (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1686647
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq1686647
    | exact resolve eq1686647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686647
  have eq1687117 : (k x y) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1687069
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq1687069
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1687069 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687069
  have eq1687143 : (k x y) = (M.op y y) := by
    first
    | (have j1 := eq124 x y
       grind)
    | (have r₁ := eq1687117
       have r₂ := eq124 x y
       grind)
    | exact resolve eq1687117 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1687117
  have eq1687161 : (M.op y x) = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1687143
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1687143
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1687143 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687143
  have eq3008193 : y = (M.op (M.op y (M.op y x)) (M.op y (M.op y x))) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1001 y y
       have i₂ := eq1687161
       grind)
    | exact superpose eq1687161 eq1001
    | exact resolve eq1001 eq1687161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq1687161
  have eq3008847 : y = (M.op (M.op y (M.op y x)) (M.op x (M.op x x))) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3008193
       have i₂ := eq10711 y x (M.op y (M.op y x))
       grind)
    | exact superpose eq10711 eq3008193
    | exact resolve eq3008193 eq10711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10711 eq3008193
  have eq3009144 : y = (M.op x (M.op (M.op y (M.op y x)) (M.op x x))) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3008847
       have i₂ := eq1260 x (M.op y (M.op y x))
       grind)
    | exact superpose eq1260 eq3008847
    | exact resolve eq3008847 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq3008847
  have eq3009292 : y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3009144
       have i₂ := eq7280 x y x
       grind)
    | exact superpose eq7280 eq3009144
    | exact resolve eq3009144 eq7280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7280 eq3009144
  have eq3009468 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 (M.op X0 x)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9598 X0 x y
       have i₂ := eq3009292
       grind)
    | exact superpose eq3009292 eq9598
    | exact resolve eq9598 eq3009292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009292
  have eq3009962 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3009468 x
       have i₂ := eq1316 x x y
       grind)
    | exact superpose eq1316 eq3009468
    | exact resolve eq3009468 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009468
  have eq3010306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97612 x
       have i₂ := eq3009962
       grind)
    | exact superpose eq3009962 eq97612
    | exact resolve eq97612 eq3009962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97612 eq3009962
  have eq3011095 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq3010306
       have r₂ := eq16
       grind)
    | exact resolve eq3010306 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3010306
  have eq3011179 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq732 y x
       have i₂ := eq3011095
       grind)
    | exact superpose eq3011095 eq732
    | exact resolve eq732 eq3011095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq3011236 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 (M.op X0 y)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9598 X0 y x
       have i₂ := eq3011095
       grind)
    | exact superpose eq3011095 eq9598
    | exact resolve eq9598 eq3011095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9598
  have eq3011345 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op X0 (σ (M.op x x)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq113297 y X0 x
       have i₂ := eq3011095
       grind)
    | exact superpose eq3011095 eq113297
    | exact resolve eq113297 eq3011095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113297 eq3011095
  have eq3011634 : (σ x) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq3011345 x
       have i₂ := eq97379 x x
       grind)
    | exact superpose eq97379 eq3011345
    | exact resolve eq3011345 eq97379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97379 eq3011345
  have eq3011670 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3011236 x
       have i₂ := eq1316 x y x
       grind)
    | exact superpose eq1316 eq3011236
    | exact resolve eq3011236 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq3011236
  have eq3011952 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq97387 y
       have i₂ := eq3011670
       grind)
    | exact superpose eq3011670 eq97387
    | exact resolve eq97387 eq3011670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97387 eq3011670
  have eq3017361 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq3011634
       have i₂ := eq3011179
       grind)
    | exact superpose eq3011179 eq3011634
    | exact resolve eq3011634 eq3011179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011179 eq3011634
  have eq3017808 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq3017361
  have eq3037766 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3011952
       grind)
    | exact superpose eq3011952 eq16
    | exact resolve eq16 eq3011952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011952
  have eq3038684 : x = y := by
    first
    | (have r₁ := eq3037766
       have r₂ := eq3017808
       grind)
    | exact resolve eq3037766 eq3017808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017808 eq3037766
  have eq3039153 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3038684
       grind)
    | exact superpose eq3038684 eq16
    | exact resolve eq16 eq3038684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3038684
  have eq3039171 : False := by grind
  exact eq3039171

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pyy_pyx_Equation947 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq79 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq196 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq222 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq652 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 X2 X1
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq878 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq889 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq878 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq890 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq879 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq879 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq879 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq879 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq891 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq889 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq889 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq889 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq889 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq900 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq890 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq890
    | (have j0 := eq890 X0 X1
       grind)
    | exact resolve eq890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq901 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq891 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq891
    | (have j0 := eq891 X0 X1
       grind)
    | exact resolve eq891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq1057 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq652 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq652
    | (have j0 := eq652 y x X0
       grind)
    | exact resolve eq652 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq652
    | (have j0 := eq652 (σ y) (σ x) X0
       grind)
    | exact resolve eq652 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq652 X1 x X0
       grind)
    | exact superpose eq652 eq14
    | exact resolve eq14 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1143 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1079 (M.op X1 X0) X0
       have i₂ := eq652 X0 X1 X0
       grind)
    | exact superpose eq652 eq1079
    | exact resolve eq1079 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X1 X0 X0
       have i₂ := eq1079 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1079 eq52
    | exact resolve eq52 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1162 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq1079 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq1079 eq14
    | exact resolve eq14 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1148 X0 X1
       have i₂ := eq652 X1 X0 X0
       grind)
    | exact superpose eq652 eq1148
    | exact resolve eq1148 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1204 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq1057 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1057
    | (have j0 := eq1057 x
       grind)
    | exact resolve eq1057 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | exact superpose eq1057 eq1079
    | exact resolve eq1079 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1305 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq1060
    | (have j0 := eq1060 (σ x)
       grind)
    | exact resolve eq1060 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1309 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq1060 eq1079
    | exact resolve eq1079 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1579 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq213 eq1143
    | exact resolve eq1143 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1581 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y y) (M.op (M.op y y) (M.op y y)))) := by
    first
    | (have i₁ := eq1143 (M.op y y) x
       have i₂ := eq1204
       grind)
    | exact superpose eq1204 eq1143
    | exact resolve eq1143 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1585 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq222 eq1143
    | exact resolve eq1143 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1587 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1305 eq1143
    | exact resolve eq1143 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1614 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq1587
       have i₂ := eq1079 (M.op sF3 sF3) sF3
       grind)
    | exact superpose eq1079 eq1587
    | exact resolve eq1587 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587
  have eq1616 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1585
       have i₂ := eq1079 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq1079 eq1585
    | exact resolve eq1585 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq1619 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq1581
       have i₂ := eq1079 (M.op y y) y
       grind)
    | exact superpose eq1079 eq1581
    | exact resolve eq1581 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1621 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1579
       have i₂ := eq1079 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq1079 eq1579
    | exact resolve eq1579 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579
  have eq1650 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1616 eq222
    | exact resolve eq222 eq1616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq1672 : y = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq1621 eq213
    | exact resolve eq213 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1677 : (M.op x y) ≠ (M.op y (M.op x y)) ∨ (M.op y (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1621 eq13
    | exact resolve eq13 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1777 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq1616 eq1614
    | exact resolve eq1614 eq1616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq1823 : (M.op y y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq1621 eq1619
    | exact resolve eq1619 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq2299 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1169 (M.op X1 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq1143 X0 X1
       grind)
    | exact superpose eq1143 eq1169
    | exact resolve eq1169 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq2307 : (M.op (M.op y (M.op y y)) y) = (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1208 eq1169
    | exact resolve eq1169 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq2315 : (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1309 eq1169
    | exact resolve eq1169 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq2319 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1079 X1 X0
       have i₂ := eq1169 X1 X0
       grind)
    | (have i₁ := eq1079 X1 X1
       have i₂ := eq1169 X1 X1
       grind)
    | exact superpose eq1169 eq1079
    | exact resolve eq1079 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2390 : (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) := by
    first
    | (have i₁ := eq2315
       have i₂ := eq652 (M.op sF3 sF3) sF3 sF3
       grind)
    | exact superpose eq652 eq2315
    | exact resolve eq2315 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2315
  have eq2398 : (M.op (M.op y (M.op y y)) y) = (M.op (M.op x y) (M.op y (M.op (M.op y y) (M.op y y)))) := by
    first
    | (have i₁ := eq2307
       have i₂ := eq652 (M.op y y) y y
       grind)
    | exact superpose eq652 eq2307
    | exact resolve eq2307 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq2405 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2299 X0 X1
       have i₂ := eq652 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq652 eq2299
    | exact resolve eq2299 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq2299
  have eq2434 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq2390
       have i₂ := eq14 sF3 sF3 sF3
       grind)
    | exact superpose eq14 eq2390
    | exact resolve eq2390 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390
  have eq2440 : (M.op (M.op x y) y) = (M.op (M.op y (M.op y y)) y) := by
    first
    | (have i₁ := eq2398
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq2398
    | exact resolve eq2398 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq2445 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2405 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2405
    | exact resolve eq2405 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2460 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq2434
       have i₂ := eq1162 sF3 sF3
       grind)
    | exact superpose eq1162 eq2434
    | exact resolve eq2434 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2434
  have eq2466 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2440
       have i₂ := eq1162 y y
       grind)
    | exact superpose eq1162 eq2440
    | exact resolve eq2440 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2440
  have eq2471 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2445 X0 X1
       have i₂ := eq1162 X0 X0
       grind)
    | exact superpose eq1162 eq2445
    | exact resolve eq2445 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq2445
  have eq6045 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78
    | (have j0 := eq78 x
       grind)
    | exact resolve eq78 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq6064 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6045
  have eq6070 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6064
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6064
    | exact resolve eq6064 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6064
  have eq6088 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6070
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6070 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6070
  have eq6093 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6088 eq49
    | exact resolve eq49 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6088
  have eq6215 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq79 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq79
    | (have j0 := eq79 y
       grind)
    | exact resolve eq79 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq6241 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6215
  have eq6247 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6241
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq6241
    | exact resolve eq6241 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq6241
  have eq6270 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6247
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6247 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6247
  have eq6291 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6270 eq107
    | exact resolve eq107 eq6270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq7085 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq196 eq13
    | (have j0 := eq13 (σ X0) (σ y)
       have j1 := eq196 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ X0)
       have r₂ := eq196 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ y)
       have r₂ := eq196 X0
       grind)
    | exact resolve eq13 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq7102 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7085 X0
       have j1 := eq13 (σ X0) (σ y)
       grind)
    | (have r₁ := eq7085 X0
       have r₂ := eq13 (σ y) (σ X0)
       grind)
    | (have r₁ := eq7085 X0
       have r₂ := eq13 (σ X0) (σ y)
       grind)
    | exact resolve eq7085 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7085
  have eq7133 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq7102
    | (have j0 := eq7102 X0
       grind)
    | exact resolve eq7102 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq7102
  have eq17988 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq17988
    | exact resolve eq17988 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17988
  have eq18000 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq17989
       have r₂ := eq27
       grind)
    | exact resolve eq17989 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17989
  have eq18002 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18000
    | exact resolve eq18000 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18000
  have eq18006 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18002 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18002
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18002
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18002
       grind)
    | exact resolve eq12 eq18002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18007 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18002 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18002
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18002
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18002
       grind)
    | exact resolve eq13 eq18002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18018 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18002 eq2319
    | exact resolve eq2319 eq18002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18002
  have eq18020 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq18007
  have eq18021 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq18006
  have eq18022 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18018
       have i₂ := eq1169 sF2 sF3
       grind)
    | exact superpose eq1169 eq18018
    | exact resolve eq18018 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18018
  have eq18025 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18020
    | exact resolve eq18020 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18020
  have eq18026 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18021
    | exact resolve eq18021 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18021
  have eq18027 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq18026
  have eq18028 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1305 eq18022
    | exact resolve eq18022 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18022
  have eq18029 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1616 eq18028
    | exact resolve eq18028 eq1616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18028
  have eq18033 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18025 eq59
    | exact resolve eq59 eq18025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq18025
  have eq18126 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18029 eq1650
    | exact resolve eq1650 eq18029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18131 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18029 eq1777
    | exact resolve eq1777 eq18029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777 eq18029
  have eq18174 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18131
    | exact resolve eq18131 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18131
  have eq18180 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18126 eq6093
    | exact resolve eq6093 eq18126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18231 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq18180
    | exact resolve eq18180 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18180
  have eq18273 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18174 eq6291
    | exact resolve eq6291 eq18174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18174
  have eq19329 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18033
       grind)
    | exact superpose eq18033 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18033
  have eq19330 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19329
  have eq19332 : x = (M.op x y) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19330
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19330
    | exact resolve eq19330 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19330
  have eq19333 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19332
  have eq19747 : y ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19333
  have eq21086 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18027 eq101
    | exact resolve eq101 eq18027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq18027
  have eq21100 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21086
  have eq21111 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21100 eq6093
    | exact resolve eq6093 eq21100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6093
  have eq21118 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21100 eq18126
    | exact resolve eq18126 eq21100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18126 eq21100
  have eq21148 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq21118
  have eq21156 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq21111
    | exact resolve eq21111 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21111
  have eq21158 : y ≠ y ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq21148
       grind)
    | exact superpose eq21148 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq21148
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq21148
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21148
       grind)
    | exact resolve eq12 eq21148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21159 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq21148
       grind)
    | exact superpose eq21148 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21148
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21148
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21148
       grind)
    | exact resolve eq13 eq21148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21170 : x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2319 x y
       have i₂ := eq21148
       grind)
    | exact superpose eq21148 eq2319
    | exact resolve eq2319 eq21148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21148
  have eq21172 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq21159
  have eq21173 : x = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq21158
  have eq21175 : x = (M.op x (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq21170
       have i₂ := eq1169 x y
       grind)
    | exact superpose eq1169 eq21170
    | exact resolve eq21170 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21170
  have eq21178 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq21172
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21172
    | exact resolve eq21172 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21172
  have eq21179 : x = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq21173
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21173
    | exact resolve eq21173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21173
  have eq21180 : (k y x) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq21179
  have eq21181 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq21175
       have i₂ := eq1204
       grind)
    | exact superpose eq1204 eq21175
    | exact resolve eq21175 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21175
  have eq21182 : x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1621 eq21181
    | exact resolve eq21181 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21181
  have eq22141 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq21178
       grind)
    | exact superpose eq21178 eq44
    | exact resolve eq44 eq21178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq21178
  have eq22172 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq22141
    | exact resolve eq22141 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22141
  have eq22207 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21182 eq1672
    | exact resolve eq1672 eq21182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21182
  have eq25789 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18231
       have i₂ := eq21156
       grind)
    | exact superpose eq21156 eq18231
    | exact resolve eq18231 eq21156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18231 eq21156
  have eq25810 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq25789
  have eq25862 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq25810
       grind)
    | exact superpose eq25810 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25810
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25810
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25810
       grind)
    | exact resolve eq13 eq25810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25873 : x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2319 x y
       have i₂ := eq25810
       grind)
    | exact superpose eq25810 eq2319
    | exact resolve eq2319 eq25810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25810
  have eq25876 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq25862
  have eq25879 : x = (M.op x (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25873
       have i₂ := eq1169 x y
       grind)
    | exact superpose eq1169 eq25873
    | exact resolve eq25873 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25873
  have eq25882 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25876
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25876
    | exact resolve eq25876 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25876
  have eq25885 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25879
       have i₂ := eq1204
       grind)
    | exact superpose eq1204 eq25879
    | exact resolve eq25879 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25879
  have eq25886 : x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1621 eq25885
    | exact resolve eq25885 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25885
  have eq26361 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq900 x y
       have i₂ := eq25882
       grind)
    | exact superpose eq25882 eq900
    | (have j0 := eq900 x y
       grind)
    | exact resolve eq900 eq25882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq25882
  have eq26366 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq26361
    | exact resolve eq26361 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26361
  have eq26382 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26366
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26366
    | exact resolve eq26366 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26366
  have eq26393 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq26382
    | exact resolve eq26382 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26382
  have eq26402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26393
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26393
    | exact resolve eq26393 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26393
  have eq26411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26402
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26402
    | exact resolve eq26402 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26402
  have eq26425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq26411
    | exact resolve eq26411 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26411
  have eq26437 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26425
       have r₂ := eq27
       grind)
    | exact resolve eq26425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26425
  have eq26445 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26437
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26437
    | exact resolve eq26437 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26437
  have eq26448 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26445
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26445
    | exact resolve eq26445 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26445
  have eq26449 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq26448
    | exact resolve eq26448 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26448
  have eq26450 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq26449
  have eq26456 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25886 eq1823
    | exact resolve eq1823 eq25886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823 eq25886
  have eq26501 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26456
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26456
    | exact resolve eq26456 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26456
  have eq28374 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq21180
       grind)
    | exact superpose eq21180 eq74
    | exact resolve eq74 eq21180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq21180
  have eq32533 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6270 eq108
    | exact resolve eq108 eq6270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq6270
  have eq36523 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28374
       have i₂ := eq22207
       grind)
    | exact superpose eq22207 eq28374
    | exact resolve eq28374 eq22207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22207 eq28374
  have eq36579 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq36523
  have eq36586 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36579
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36579
    | exact resolve eq36579 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36579
  have eq36604 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq36586 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq36586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36586
  have eq36622 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq36604
    | exact resolve eq36604 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36604
  have eq36634 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq36622
    | exact resolve eq36622 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36622
  have eq36635 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq36634
  have eq39266 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq36635 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq36635
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq36635
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq36635
       grind)
    | exact resolve eq13 eq36635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36635
  have eq39280 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq39266
  have eq39285 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq39280
    | exact resolve eq39280 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39280
  have eq41340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39285 eq22172
    | exact resolve eq22172 eq39285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22172 eq39285
  have eq41353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq41340
  have eq41358 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41353
       have r₂ := eq27
       grind)
    | exact resolve eq41353 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41353
  have eq41373 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41358 eq1650
    | exact resolve eq1650 eq41358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41405 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq41418 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1305 eq41373
    | exact resolve eq41373 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305 eq41373
  have eq41424 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1616 eq41418
    | exact resolve eq41418 eq1616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616 eq41418
  have eq41496 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41358 eq41424
    | exact resolve eq41424 eq41358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41358 eq41424
  have eq41543 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41496
  have eq41566 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41543
       have r₂ := eq41405
       grind)
    | exact resolve eq41543 eq41405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41405 eq41543
  have eq42328 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41566 eq6291
    | exact resolve eq6291 eq41566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41566
  have eq42425 : y = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq42328
    | exact resolve eq42328 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq42328
  have eq42874 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq42425
       grind)
    | exact superpose eq42425 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq42425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42425
  have eq42896 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq42874
  have eq43209 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26501
       have i₂ := eq42896
       grind)
    | exact superpose eq42896 eq26501
    | exact resolve eq26501 eq42896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26501 eq42896
  have eq43282 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq43209
  have eq43306 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq43282
       have r₂ := eq26450
       grind)
    | exact resolve eq43282 eq26450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26450 eq43282
  have eq43344 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43306 eq1650
    | exact resolve eq1650 eq43306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650 eq43306
  have eq43713 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43344 eq2319
    | exact resolve eq2319 eq43344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43344
  have eq43762 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43713 eq6291
    | exact resolve eq6291 eq43713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43713
  have eq43853 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq43762
    | exact resolve eq43762 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq43762
  have eq43876 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq43853
       grind)
    | exact superpose eq43853 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq43853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43893 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq43876
  have eq371344 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq43893
       grind)
    | exact superpose eq43893 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq43893
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq43893
       grind)
    | exact resolve eq13 eq43893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371374 : x ≠ y ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq43893
  have eq371375 : y = (k y y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq371344
  have eq401402 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43853
       have i₂ := eq371375
       grind)
    | exact superpose eq371375 eq43853
    | exact resolve eq43853 eq371375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43853 eq371375
  have eq401503 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq401402
  have eq401554 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq401503
       have r₂ := eq371374
       grind)
    | exact resolve eq401503 eq371374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371374 eq401503
  have eq401755 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2471 y y
       have i₂ := eq401554
       grind)
    | exact superpose eq401554 eq2471
    | exact resolve eq2471 eq401554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401554
  have eq401782 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq401755
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq401755
    | exact resolve eq401755 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401755
  have eq401783 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq401782
  have eq401805 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq401783 eq20
    | exact resolve eq20 eq401783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401887 : y = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq401783 eq1672
    | exact resolve eq1672 eq401783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq402058 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq402147 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq401887
       have i₂ := eq1204
       grind)
    | exact superpose eq1204 eq401887
    | exact resolve eq401887 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204 eq401887
  have eq402221 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq401805
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq401805
    | exact resolve eq401805 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401805
  have eq402224 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1621 eq402147
    | exact resolve eq402147 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621 eq402147
  have eq402262 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq402221 eq26
    | exact resolve eq26 eq402221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402336 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq402221 eq2460
    | exact resolve eq2460 eq402221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460
  have eq403128 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq402224 eq1677
    | exact resolve eq1677 eq402224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677 eq402224
  have eq403250 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq403128
       have r₂ := eq401783
       grind)
    | exact resolve eq403128 eq401783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403128
  have eq403382 : y = (k y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq401783 eq403250
    | exact resolve eq403250 eq401783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401783
  have eq403424 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq403250 eq887
    | (have j0 := eq887 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq887 eq403250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq403250
  have eq403429 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq403424
  have eq403444 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq403429
    | exact resolve eq403429 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403429
  have eq403483 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq403382
       have r₂ := eq402058
       grind)
    | exact resolve eq403382 eq402058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402058 eq403382
  have eq403487 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq403444
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq403444
    | exact resolve eq403444 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403444
  have eq403520 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq403487
       have r₂ := eq402221
       grind)
    | exact resolve eq403487 eq402221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403487
  have eq403550 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq403520
    | exact resolve eq403520 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403520
  have eq403811 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18273
       have i₂ := eq403483
       grind)
    | exact superpose eq403483 eq18273
    | exact resolve eq18273 eq403483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18273 eq403483
  have eq403942 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq403811
  have eq403980 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq403942
       have r₂ := eq19747
       grind)
    | exact resolve eq403942 eq19747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19747 eq403942
  have eq404343 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq403550 eq1079
    | exact resolve eq1079 eq403550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq403550
  have eq432515 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq402336 eq404343
    | exact resolve eq404343 eq402336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402336 eq404343
  have eq432638 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq432515
  have eq432711 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq432638
       have i₂ := eq1169 sF4 sF1
       grind)
    | exact superpose eq1169 eq432638
    | exact resolve eq432638 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq432638
  have eq446861 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq432711 eq2319
    | exact resolve eq2319 eq432711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319 eq432711
  have eq522722 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq403980
       grind)
    | exact superpose eq403980 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq403980
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq403980
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq403980
       grind)
    | exact resolve eq13 eq403980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403980
  have eq522754 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq522722
  have eq522795 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq522754
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq522754
    | exact resolve eq522754 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522754
  have eq527459 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7133 x
       have i₂ := eq522795
       grind)
    | exact superpose eq522795 eq7133
    | (have j0 := eq7133 x
       grind)
    | exact resolve eq7133 eq522795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7133 eq522795
  have eq527537 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq527459
    | exact resolve eq527459 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527459
  have eq527580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq527537
       have r₂ := eq402221
       grind)
    | exact resolve eq527537 eq402221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402221 eq527537
  have eq527614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq527580
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq527580
    | exact resolve eq527580 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527580
  have eq527646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq527614
    | exact resolve eq527614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527614
  have eq527682 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq527646
    | exact resolve eq527646 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527646
  have eq527709 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq527682
       have r₂ := eq27
       grind)
    | exact resolve eq527682 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527682
  have eq527722 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq527709
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq527709
    | exact resolve eq527709 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527709
  have eq527730 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq527722
    | exact resolve eq527722 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527722
  have eq527731 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq527730
  have eq528262 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq527731 eq446861
    | exact resolve eq446861 eq527731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446861 eq527731
  have eq528311 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq528262
  have eq528804 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq528311 eq402262
    | exact resolve eq402262 eq528311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402262 eq528311
  have eq528877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq528804
  have eq528913 : x = (M.op x y) := by
    first
    | (have r₁ := eq528877
       have r₂ := eq27
       grind)
    | exact resolve eq528877 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528877
  have eq528922 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq528913 eq20
    | exact resolve eq20 eq528913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq529031 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq528913 eq2466
    | exact resolve eq2466 eq528913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466
  have eq529217 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq529031
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq529031
    | exact resolve eq529031 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq529031
  have eq529301 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq528922
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq528922
    | exact resolve eq528922 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528922
  have eq529304 : x = (M.op y y) := by
    first
    | exact superpose eq528913 eq529217
    | exact resolve eq529217 eq528913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529217
  have eq529339 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq529301 eq26
    | exact resolve eq26 eq529301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq530288 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq32533
       have i₂ := eq529304
       grind)
    | exact superpose eq529304 eq32533
    | exact resolve eq32533 eq529304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32533
  have eq530418 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq529304
       grind)
    | exact superpose eq529304 eq13
    | exact resolve eq13 eq529304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529304
  have eq530492 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq530288
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq530288
    | exact resolve eq530288 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530288
  have eq530513 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq529301 eq530492
    | exact resolve eq530492 eq529301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530492
  have eq569164 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq530513 eq6291
    | exact resolve eq6291 eq530513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6291
  have eq569440 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq530513 eq2471
    | exact resolve eq2471 eq530513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471 eq530513
  have eq569463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq529339 eq569440
    | exact resolve eq569440 eq529339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569440
  have eq569501 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq569164
    | exact resolve eq569164 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq569164
  have eq569505 : x = y := by
    first
    | (have r₁ := eq569463
       have r₂ := eq27
       grind)
    | exact resolve eq569463 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569463
  have eq569531 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq528913 eq569501
    | exact resolve eq569501 eq528913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528913 eq569501
  have eq569542 : x = (k y y) := by
    first
    | (have r₁ := eq569531
       have r₂ := eq530418
       grind)
    | exact resolve eq569531 eq530418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530418 eq569531
  have eq569553 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq569505
       grind)
    | exact superpose eq569505 eq24
    | exact resolve eq24 eq569505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq570349 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq569553
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq569553
    | exact resolve eq569553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569553
  have eq570530 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq529301 eq570349
    | exact resolve eq570349 eq529301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570349
  have eq571321 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq570530 eq529339
    | exact resolve eq529339 eq570530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529339 eq570530
  have eq575092 : x = (k x x) := by
    first
    | (have i₁ := eq569542
       have i₂ := eq569505
       grind)
    | exact superpose eq569505 eq569542
    | exact resolve eq569542 eq569505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569505 eq569542
  have eq575157 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq901 x x
       have i₂ := eq575092
       grind)
    | exact superpose eq575092 eq901
    | (have j0 := eq901 x x
       grind)
    | exact resolve eq901 eq575092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq575092
  have eq575167 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq575157
  have eq575168 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq575167
  have eq575201 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq575168
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq575168
    | exact resolve eq575168 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq575168
  have eq575249 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq529301 eq575201
    | exact resolve eq575201 eq529301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529301 eq575201
  have eq579973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq575249 eq571321
    | exact resolve eq571321 eq575249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571321 eq575249
  have eq579974 : False := by grind
  exact eq579974

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_y_pyy_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq100 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq105 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq101
    | exact resolve eq101 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq105
    | exact resolve eq105 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq145 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq16
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq236 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq34
    | exact resolve eq34 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq323 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq312 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq312
    | exact resolve eq312 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq326 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq323
    | exact resolve eq323 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq323
  have eq520 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq614 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq609
    | exact resolve eq609 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq654 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq817 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq16
    | exact resolve eq16 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq969 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq817 X0
       grind)
    | exact superpose eq817 eq50
    | exact resolve eq50 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq1429 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq239 eq50
    | exact resolve eq50 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1450 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq236 eq1429
    | exact resolve eq1429 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1936 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq570 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq570 X0 X0 X0
       grind)
    | exact superpose eq570 eq570
    | exact resolve eq570 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1938 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq239 eq570
    | exact resolve eq570 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq1957 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq570 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq570 X0 X0 X0
       grind)
    | exact superpose eq570 eq570
    | exact resolve eq570 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1988 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq570 X0 X0 X0
       grind)
    | exact superpose eq570 eq14
    | exact resolve eq14 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1989 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq570 X0 X0 X0
       grind)
    | exact superpose eq570 eq50
    | exact resolve eq50 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1990 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq570 X0 X0 X0
       grind)
    | exact superpose eq570 eq51
    | exact resolve eq51 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1997 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq520 (M.op x (M.op x x))
       have i₂ := eq570 x x x
       grind)
    | exact superpose eq570 eq520
    | exact resolve eq520 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq2000 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq603 (M.op x (M.op x x)) x
       have i₂ := eq570 x x x
       grind)
    | exact superpose eq570 eq603
    | exact resolve eq603 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq603
  have eq2037 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq236 eq1938
    | exact resolve eq1938 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq2053 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op y (M.op y (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1450 eq2037
    | exact resolve eq2037 eq1450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450 eq2037
  have eq2214 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq529 X0
       have i₂ := eq1989 X0
       grind)
    | exact superpose eq1989 eq529
    | exact resolve eq529 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq2221 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq533 X0 X0
       have i₂ := eq1989 X0
       grind)
    | exact superpose eq1989 eq533
    | exact resolve eq533 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2242 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1989 eq532
    | exact resolve eq532 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2255 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq532 eq2242
    | exact resolve eq2242 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq2294 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq654 eq2214
    | exact resolve eq2214 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq2413 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1990 X0
       have i₂ := eq1989 X0
       grind)
    | exact superpose eq1989 eq1990
    | exact resolve eq1990 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2443 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1990 eq532
    | exact resolve eq532 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq2456 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq532 eq2443
    | exact resolve eq2443 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq2443
  have eq2535 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1997 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1997
    | exact resolve eq1997 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997
  have eq2581 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2535 X0 X1
       have i₂ := eq1989 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq1989 eq2535
    | exact resolve eq2535 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535
  have eq2598 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2581 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2581
    | exact resolve eq2581 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2581
  have eq2763 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2000 X0 X1
       have i₂ := eq1989 X0
       grind)
    | exact superpose eq1989 eq2000
    | exact resolve eq2000 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq3004 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq969 eq2214
    | exact resolve eq2214 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq2214
  have eq5333 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X1 X0 X1 X0
       have i₂ := eq614 X0 X1
       grind)
    | exact superpose eq614 eq535
    | exact resolve eq535 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq614
  have eq29887 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq593 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1988 X0 X0 X1
       grind)
    | exact superpose eq1988 eq593
    | exact resolve eq593 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988
  have eq29975 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29887 X0 X1 x x x
       have i₂ := eq593 X0 X0 x x x
       grind)
    | exact superpose eq593 eq29887
    | exact resolve eq29887 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq29887
  have eq43998 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2598 eq14
    | exact resolve eq14 eq2598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq44785 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1936 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1936
    | (have j0 := eq1936 y x X0
       grind)
    | exact resolve eq1936 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq46722 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq43998 eq1957
    | exact resolve eq1957 eq43998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq47315 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq236 eq46722
    | exact resolve eq46722 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq46722
  have eq47616 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47315 X0 X1
       have i₂ := eq1989 (M.op X0 (M.op y X0))
       grind)
    | exact superpose eq1989 eq47315
    | exact resolve eq47315 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989 eq47315
  have eq47779 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq533 eq47616
    | exact resolve eq47616 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq47616
  have eq50441 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op y (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq47779 eq2053
    | exact resolve eq2053 eq47779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053 eq47779
  have eq71085 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44785 y
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq44785
    | exact resolve eq44785 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq44785
  have eq71237 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71085
       have i₂ := eq29975 (M.op y x) y
       grind)
    | exact superpose eq29975 eq71085
    | exact resolve eq71085 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29975 eq71085
  have eq71272 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71237
       have i₂ := eq53 y x
       grind)
    | exact superpose eq53 eq71237
    | exact resolve eq71237 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq71237
  have eq71290 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq43998 eq71272
    | exact resolve eq71272 eq43998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43998 eq71272
  have eq71321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71290 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq71290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71290
  have eq71322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq71321
    | exact resolve eq71321 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71321
  have eq71333 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq71322
       have r₂ := eq27
       grind)
    | exact resolve eq71322 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71322
  have eq71337 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq71333
    | exact resolve eq71333 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71333
  have eq71343 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71337 eq145
    | exact resolve eq145 eq71337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq71361 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71337 eq50
    | exact resolve eq50 eq71337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq71337
  have eq71755 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71361 eq5333
    | exact resolve eq5333 eq71361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5333 eq71361
  have eq71851 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq71755
    | exact resolve eq71755 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71755
  have eq71893 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71851 eq2763
    | exact resolve eq2763 eq71851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763 eq71851
  have eq78752 : (M.op (σ y) (σ x)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71893 eq2413
    | exact resolve eq2413 eq71893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413 eq71893
  have eq78859 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2221 eq78752
    | exact resolve eq78752 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221 eq78752
  have eq78886 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq78859 eq71343
    | exact resolve eq71343 eq78859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71343 eq78859
  have eq78957 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq78886
  have eq78962 : (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq71 eq78957
    | exact resolve eq78957 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78957
  have eq80688 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq50441 X0 y
       have i₂ := eq78962
       grind)
    | exact superpose eq78962 eq50441
    | exact resolve eq50441 eq78962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78962
  have eq80777 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq50441 eq80688
    | exact resolve eq80688 eq50441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50441 eq80688
  have eq80778 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq80777
  have eq80990 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq80778 eq2456
    | exact resolve eq2456 eq80778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2456
  have eq81036 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq80990
    | exact resolve eq80990 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80990
  have eq84920 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq81036 eq3004
    | exact resolve eq3004 eq81036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004 eq81036
  have eq85035 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq84920
    | exact resolve eq84920 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq84920
  have eq86824 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq80778 eq85035
    | exact resolve eq85035 eq80778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80778 eq85035
  have eq86902 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq86824
  have eq86928 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq86902
    | exact resolve eq86902 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq86902
  have eq86944 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86928
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86928
    | exact resolve eq86928 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86928
  have eq86945 : x = (M.op x y) ∨ x = y := by grind
  clear eq86944
  have eq87199 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq86945 eq20
    | exact resolve eq20 eq86945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87319 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq86945 eq2255
    | exact resolve eq2255 eq86945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2255 eq86945
  have eq87413 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq87319
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87319
    | exact resolve eq87319 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87319
  have eq87477 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq87199
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq87199
    | exact resolve eq87199 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87199
  have eq87511 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq87477 eq26
    | exact resolve eq26 eq87477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87477
  have eq87837 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2294 y
       have i₂ := eq87413
       grind)
    | exact superpose eq87413 eq2294
    | exact resolve eq2294 eq87413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294 eq87413
  have eq87968 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq87837
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87837
    | exact resolve eq87837 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87837
  have eq88043 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq87968
    | exact resolve eq87968 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87968
  have eq88756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq88043 eq87511
    | exact resolve eq87511 eq88043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87511 eq88043
  have eq88823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq88756
  have eq88844 : x = y := by
    first
    | (have r₁ := eq88823
       have r₂ := eq27
       grind)
    | exact resolve eq88823 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88823
  have eq88856 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq88844
       grind)
    | exact superpose eq88844 eq18
    | exact resolve eq18 eq88844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq88857 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq88844
       grind)
    | exact superpose eq88844 eq24
    | exact resolve eq24 eq88844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq88844
  have eq89133 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq88857
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq88857
    | exact resolve eq88857 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq88857
  have eq89181 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq89133 eq26
    | exact resolve eq26 eq89133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq89133
  have eq89993 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq89181 eq71
    | exact resolve eq71 eq89181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq89181
  have eq90294 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq89993
       have i₂ := eq88856
       grind)
    | exact superpose eq88856 eq89993
    | exact resolve eq89993 eq88856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88856 eq89993
  have eq90438 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90294 eq15
    | exact resolve eq15 eq90294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90294
  have eq90552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq90438
    | exact resolve eq90438 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq90438
  have eq90593 : False := by grind
  exact eq90593

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_y_pxx_x_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq85 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq85
    | exact resolve eq85 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq85
  have eq97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq107 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 x y
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq206 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0) (σ X0)
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq25
    | exact resolve eq25 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq9
    | exact resolve eq9 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq206 X0
       have i₂ := eq97 (M.op X0 X0)
       grind)
    | exact superpose eq97 eq206
    | exact resolve eq206 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq218 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq215 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq215
    | exact resolve eq215 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq383 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X2 (M.op X3 X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq24 X2 (σ x) (M.op (σ (M.op x x)) (M.op X0 X0)) X3
       have i₂ := eq207 x X0
       grind)
    | exact superpose eq207 eq24
    | exact resolve eq24 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq704 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq383 X0 X0 X0
       grind)
    | exact superpose eq383 eq9
    | exact resolve eq9 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq834 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107 X2
       have i₂ := eq704 X2 X0 X1
       grind)
    | exact superpose eq704 eq107
    | exact resolve eq107 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq834 (M.op X2 (M.op X0 X0)) (M.op (M.op x x) (M.op X2 X2)) X1
       have i₂ := eq24 X2 x x X0
       grind)
    | exact superpose eq24 eq834
    | exact resolve eq834 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq834
  have eq1067 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq156
       have i₂ := eq97 x
       grind)
    | exact superpose eq97 eq156
    | exact resolve eq156 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq1068 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq1067
       have i₂ := eq97 y
       grind)
    | exact superpose eq97 eq1067
    | exact resolve eq1067 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1069 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1068
       have i₂ := eq97 x
       grind)
    | exact superpose eq97 eq1068
    | exact resolve eq1068 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1069
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1069
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1069 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1111 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq1110
  have eq1161 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112 X0 (M.op X1 X0) X2 X3
       have i₂ := eq704 X0 X0 X1
       grind)
    | exact superpose eq704 eq112
    | exact resolve eq112 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq1173 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq112 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq112 eq112
    | exact resolve eq112 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1161 X0 X1 x x
       have i₂ := eq112 X0 X0 x x
       grind)
    | exact superpose eq112 eq1161
    | exact resolve eq1161 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq1161
  have eq1738 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq122 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X2 X3 X4
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq122
    | exact resolve eq122 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq1833 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1738 X0 x X2 X3 X4
       have i₂ := eq1209 (M.op X0 X0) x
       grind)
    | exact superpose eq1209 eq1738
    | exact resolve eq1738 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209 eq1738
  have eq1864 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1833 X0 X2 X3 X4
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq1833
    | exact resolve eq1833 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1833
  have eq8963 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X2 X2)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1864 X1 X0 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq1864
    | exact resolve eq1864 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1864
  have eq25304 : (M.op x x) = (τ (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1111
       grind)
    | exact superpose eq1111 eq10
    | exact resolve eq10 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq25367 : y = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq25304
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq25304
    | exact resolve eq25304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25304
  have eq25368 : (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq25367
  have eq86962 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1173 X1 X1 X1
       have i₂ := eq8963 X0 X1 X2
       grind)
    | exact superpose eq8963 eq1173
    | exact resolve eq1173 eq8963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173 eq8963
  have eq87937 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86962 X0 X1 X2
       have i₂ := eq893 X1 X2 X0
       grind)
    | exact superpose eq893 eq86962
    | exact resolve eq86962 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq86962
  have eq1014935 : (M.op y y) = (τ (σ (M.op x x))) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq25368
       grind)
    | exact superpose eq25368 eq10
    | exact resolve eq10 eq25368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25368
  have eq1015390 : (M.op x x) = (M.op y y) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1014935
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1014935
    | exact resolve eq1014935 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014935
  have eq1015391 : y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq1015390
  have eq1015551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq218 x
       have i₂ := eq1015391
       grind)
    | exact superpose eq1015391 eq218
    | exact resolve eq218 eq1015391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq1015391
  have eq1016513 : (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq1015551
       have r₂ := eq16
       grind)
    | exact resolve eq1015551 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015551
  have eq1017204 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op X0 (M.op x x)) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq87937 X0 y y
       have i₂ := eq1016513
       grind)
    | exact superpose eq1016513 eq87937
    | exact resolve eq87937 eq1016513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87937 eq1016513
  have eq1017436 : x = y := by
    first
    | (have i₁ := eq1017204 x
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq1017204
    | exact resolve eq1017204 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017204
  have eq1017756 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1017436
       grind)
    | exact superpose eq1017436 eq16
    | exact resolve eq16 eq1017436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017436
  have eq1017757 : False := by grind
  exact eq1017757
