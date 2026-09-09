import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation359`: `x ◇ x = (x ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pxy_Equation359 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law359 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law359.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq45 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq52 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq45
  have eq726 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq10
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq4443 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq411 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq4445 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4443 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq4446 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4445
  have eq4582 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4446 (σ X0)
       grind)
    | exact superpose eq4446 eq15
    | exact resolve eq15 eq4446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4601 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4582 X0
       have i₂ := eq4446 X0
       grind)
    | exact superpose eq4446 eq4582
    | exact resolve eq4582 eq4446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4446 eq4582
  have eq5243 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0)
       have i₂ := eq4601 X0
       grind)
    | exact superpose eq4601 eq9
    | exact resolve eq9 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5246 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq5308 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5246 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq5246
    | exact resolve eq5246 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5246
  have eq5325 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5308
  have eq7651 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq52
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq8002 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7651 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7651
    | (have j0 := eq7651 X0 X1
       grind)
    | exact resolve eq7651 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7651
  have eq36201 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq726 X1 X0
       grind)
    | exact superpose eq726 eq10
    | (have j1 := eq726 X1 X0
       grind)
    | exact resolve eq10 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq36635 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36201 X0 X1
       have i₂ := eq4601 X0
       grind)
    | exact superpose eq4601 eq36201
    | (have j0 := eq36201 X0 X1
       grind)
    | exact resolve eq36201 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36201
  have eq37232 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36635 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq36635
    | (have j0 := eq36635 X0 X1
       grind)
    | exact resolve eq36635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36635
  have eq37752 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37232 X0 X1
       have i₂ := eq4601 X1
       grind)
    | exact superpose eq4601 eq37232
    | (have j0 := eq37232 X0 X1
       grind)
    | exact resolve eq37232 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4601 eq37232
  have eq38113 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37752 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq37752
    | (have j0 := eq37752 X0 X1
       grind)
    | exact resolve eq37752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37752
  have eq132461 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38113 x y
       grind)
    | exact superpose eq38113 eq16
    | (have j1 := eq38113 x y
       grind)
    | exact resolve eq16 eq38113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38113
  have eq132543 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq8002 x y
       grind)
    | (have r₁ := eq132461
       have r₂ := eq8002 y x
       grind)
    | exact resolve eq132461 eq8002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8002 eq132461
  have eq134371 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq132543
       grind)
    | exact superpose eq132543 eq9
    | exact resolve eq9 eq132543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134405 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5243 y
       have i₂ := eq132543
       grind)
    | exact superpose eq132543 eq5243
    | exact resolve eq5243 eq132543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5243 eq132543
  have eq144844 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134405
       grind)
    | exact superpose eq134405 eq16
    | exact resolve eq16 eq134405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134405
  have eq145649 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq144844
       have i₂ := eq134371
       grind)
    | exact superpose eq134371 eq144844
    | exact resolve eq144844 eq134371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134371 eq144844
  have eq145650 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by grind
  clear eq145649
  have eq145651 : y = (M.op x x) := by grind
  clear eq145650
  have eq147831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5325 x
       have i₂ := eq145651
       grind)
    | exact superpose eq145651 eq5325
    | exact resolve eq5325 eq145651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5325 eq145651
  have eq147911 : False := by grind
  exact eq147911

/-- `Equation3659`: `x ◇ x = (x ◇ x) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation3659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq38
    | exact resolve eq38 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq41
    | exact resolve eq41 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq41
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq92 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq94 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq86 X1 X0
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq88 X1 X0
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq88 X1 X1
       have r₂ := eq86 X1 X1
       grind)
    | exact resolve eq88 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq88
  have eq97 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq141 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq10
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq166 X0
       grind)
    | exact superpose eq166 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq94
    | (have j0 := eq94 (σ X1) (σ X0)
       grind)
    | exact resolve eq94 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k X0 (τ X1)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq94 (τ X1) X0
       grind)
    | exact superpose eq94 eq18
    | (have j1 := eq94 (τ X1) X0
       grind)
    | exact resolve eq18 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq94 X1 (τ X0)
       grind)
    | exact superpose eq94 eq17
    | (have j1 := eq94 X1 (τ X0)
       grind)
    | exact resolve eq17 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq94
  have eq358 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq341
    | (have j0 := eq341 X0 X1
       grind)
    | exact resolve eq341 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq372 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq313 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq313
    | (have j0 := eq313 X0 X1
       grind)
    | exact resolve eq313 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq376 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq358 X0 X1
       have i₂ := eq166 X0
       grind)
    | exact superpose eq166 eq358
    | (have j0 := eq358 X0 X1
       grind)
    | exact resolve eq358 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq358
  have eq385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq372
    | (have j0 := eq372 X0 X1
       grind)
    | exact resolve eq372 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq1375 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq97 X0 X1
       grind)
    | exact resolve eq12 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1386 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1434 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1375 X0 X1
       have j1 := eq141 X0 (σ X1)
       grind)
    | (have r₁ := eq1375 X0 X0
       have r₂ := eq141 X0 (σ X0)
       grind)
    | (have r₁ := eq1375 X0 X1
       have r₂ := eq141 X0 (σ X1)
       grind)
    | exact resolve eq1375 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1375
  have eq1502 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1434 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq1434
    | (have j0 := eq1434 X0 X1
       grind)
    | exact resolve eq1434 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq1536 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1502 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq1502
    | (have j0 := eq1502 X0 X1
       grind)
    | exact resolve eq1502 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq1556 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1536 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1536
    | (have j0 := eq1536 X0 X1
       grind)
    | exact resolve eq1536 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq4979 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq321
    | exact resolve eq321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq5193 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4979 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4979
    | (have j0 := eq4979 X0 X1
       grind)
    | exact resolve eq4979 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4979
  have eq6020 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq287 X0 X1
       have i₂ := eq376 X0 X1
       grind)
    | exact superpose eq376 eq287
    | (have j0 := eq287 X0 X1
       have j1 := eq376 X0 X1
       grind)
    | (have r₁ := eq287 X0 X1
       have r₂ := eq376 X0 X1
       grind)
    | exact resolve eq287 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq376
  have eq6220 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq6020 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6020
  have eq11810 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1556 (τ X1) (τ X0)
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq1556
    | (have j0 := eq1556 (τ X0) (τ X1)
       grind)
    | exact resolve eq1556 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq11905 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11810 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11810
    | (have j0 := eq11810 X0 X1
       grind)
    | exact resolve eq11810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11810
  have eq11943 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11905 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq11905
    | (have j0 := eq11905 X0 X1
       grind)
    | exact resolve eq11905 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11905
  have eq11970 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11943 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11943
    | (have j0 := eq11943 X0 X1
       grind)
    | exact resolve eq11943 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11943
  have eq11990 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11970 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq11970
    | (have j0 := eq11970 X0 X1
       grind)
    | exact resolve eq11970 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11970
  have eq12002 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11990 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11990
    | (have j0 := eq11990 X0 X1
       grind)
    | exact resolve eq11990 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11990
  have eq12010 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12002 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12002
    | (have j0 := eq12002 X0 X1
       grind)
    | exact resolve eq12002 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12002
  have eq12014 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12010 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq12010
    | (have j0 := eq12010 X0 X1
       grind)
    | exact resolve eq12010 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12010
  have eq14858 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq385 X0 X1
       grind)
    | exact superpose eq385 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq385 X0 X1
       grind)
    | exact resolve eq13 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq15004 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14858 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq14858
    | (have j0 := eq14858 X0 X1
       grind)
    | exact resolve eq14858 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14858
  have eq15138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15004 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq15004
    | (have j0 := eq15004 X0 X1
       grind)
    | exact resolve eq15004 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15004
  have eq15139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq15138 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15138
  have eq15231 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15139 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq15139
    | (have j0 := eq15139 X0 X1
       grind)
    | exact resolve eq15139 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15139
  have eq15259 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15231 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq15231
    | (have j0 := eq15231 X0 X1
       grind)
    | exact resolve eq15231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15231
  have eq15260 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq15259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15259
  have eq83707 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq6220 X1 (τ X0)
       grind)
    | exact superpose eq6220 eq18
    | (have j1 := eq6220 X1 (τ X0)
       grind)
    | exact resolve eq18 eq6220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83749 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X1)
       have i₂ := eq6220 (σ X0) X1
       grind)
    | exact superpose eq6220 eq29
    | (have j1 := eq6220 (σ X0) X1
       grind)
    | exact resolve eq29 eq6220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6220
  have eq83788 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83749 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq83749
    | (have j0 := eq83749 X0 X1
       grind)
    | exact resolve eq83749 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83749
  have eq83802 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83707 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq83707
    | (have j0 := eq83707 X0 X1
       grind)
    | exact resolve eq83707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83707
  have eq83831 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83788 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83788
    | (have j0 := eq83788 X0 X1
       grind)
    | exact resolve eq83788 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83788
  have eq83836 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83802 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq83802
    | (have j0 := eq83802 X0 X1
       grind)
    | exact resolve eq83802 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83802
  have eq83857 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83831 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq83831
    | (have j0 := eq83831 X0 X1
       grind)
    | exact resolve eq83831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83831
  have eq83862 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83836 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83836
    | (have j0 := eq83836 X0 X1
       grind)
    | exact resolve eq83836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83836
  have eq83873 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83857 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83857
    | (have j0 := eq83857 X0 X1
       grind)
    | exact resolve eq83857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83857
  have eq83876 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq83862 X0 X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq83862
    | (have j0 := eq83862 X0 X1
       grind)
    | exact resolve eq83862 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq83862
  have eq83880 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83873 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83873
    | (have j0 := eq83873 X0 X1
       grind)
    | exact resolve eq83873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83873
  have eq85723 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq83880 (σ X0) X1
       grind)
    | exact superpose eq83880 eq29
    | (have j1 := eq83880 (σ X0) X1
       grind)
    | exact resolve eq29 eq83880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83880
  have eq85782 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85723 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq85723
    | (have j0 := eq85723 X0 X1
       grind)
    | exact resolve eq85723 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85723
  have eq85933 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85782 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq85782
    | (have j0 := eq85782 X0 X1
       grind)
    | exact resolve eq85782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85782
  have eq89190 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12014 X1 X0
       have i₂ := eq83876 X0 X1
       grind)
    | exact superpose eq83876 eq12014
    | (have j0 := eq12014 X0 X1
       have j1 := eq83876 X1 X0
       grind)
    | (have r₁ := eq12014 X1 X0
       have r₂ := eq83876 X0 X1
       grind)
    | (have r₁ := eq12014 X1 X1
       have r₂ := eq83876 X1 X1
       grind)
    | exact resolve eq12014 eq83876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12014
  have eq89275 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq83876 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83876
  have eq89289 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq89190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89190
  have eq89364 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq89289 X0 X1
       have j1 := eq89275 X0 X1
       grind)
    | (have r₁ := eq89289 X0 X1
       have r₂ := eq89275 X0 X1
       grind)
    | (have r₁ := eq89289 X1 X0
       have r₂ := eq89275 X0 X1
       grind)
    | (have r₁ := eq89289 X1 X1
       have r₂ := eq89275 X1 X1
       grind)
    | exact resolve eq89289 eq89275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89275 eq89289
  have eq102592 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89364 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89364
    | (have j0 := eq89364 (σ X0) X1
       grind)
    | exact resolve eq89364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89364
  have eq102656 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102592 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq102592
    | (have j0 := eq102592 X0 X1
       grind)
    | exact resolve eq102592 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq102592
  have eq131322 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq85933 X1 (σ X0)
       grind)
    | exact superpose eq85933 eq22
    | (have j1 := eq85933 X1 (σ X0)
       grind)
    | exact resolve eq22 eq85933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85933
  have eq131333 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131322 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq131322
    | (have j0 := eq131322 X0 X1
       grind)
    | exact resolve eq131322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131322
  have eq131371 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131333 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq131333
    | (have j0 := eq131333 X0 X1
       grind)
    | exact resolve eq131333 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131333
  have eq131401 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131371 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq131371
    | (have j0 := eq131371 X0 X1
       grind)
    | exact resolve eq131371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131371
  have eq131422 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131401 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq131401
    | (have j0 := eq131401 X0 X1
       grind)
    | exact resolve eq131401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131401
  have eq131434 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq131422 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq131422
    | (have j0 := eq131422 X0 X1
       grind)
    | exact resolve eq131422 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131422
  have eq138288 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (k x y) ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131434 y x
       grind)
    | exact superpose eq131434 eq16
    | (have j1 := eq131434 y x
       grind)
    | exact resolve eq16 eq131434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131434
  have eq138920 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq138288
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq138288
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq138288 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138924 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k x y) ∨ (M.op y y) = (k x y) ∨ (M.op x x) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq138288
       have i₂ := eq5193 y x
       grind)
    | exact superpose eq5193 eq138288
    | (have j1 := eq5193 y x
       grind)
    | (have r₁ := eq138288
       have r₂ := eq5193 y x
       grind)
    | exact resolve eq138288 eq5193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5193 eq138288
  have eq138932 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k x y) ∨ (M.op y y) = (k x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq138924
  have eq138933 : (M.op x x) = (k x y) ∨ (M.op y y) = (k x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq138932
  have eq138938 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq138920
  have eq138939 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq138938
  have eq138941 : (M.op y y) = (k x y) ∨ (M.op x x) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq138933
       have r₂ := eq12 x y
       grind)
    | exact resolve eq138933 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138933
  have eq140218 : (M.op y y) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by grind
  clear eq138941
  have eq187081 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq102656 X1 (σ X0)
       grind)
    | exact superpose eq102656 eq22
    | (have j1 := eq102656 X1 (σ X0)
       grind)
    | exact resolve eq22 eq102656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq102656
  have eq187086 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq187081 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq187081
    | (have j0 := eq187081 X0 X1
       grind)
    | exact resolve eq187081 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187081
  have eq187099 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq187086 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq187086
    | (have j0 := eq187086 X0 X1
       grind)
    | exact resolve eq187086 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187086
  have eq187106 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq187099 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq187099
    | (have j0 := eq187099 X0 X1
       grind)
    | exact resolve eq187099 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187099
  have eq187110 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq187106 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq187106
    | (have j0 := eq187106 X0 X1
       grind)
    | exact resolve eq187106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187106
  have eq187111 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq187110 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq187110
    | (have j0 := eq187110 X0 X1
       grind)
    | exact resolve eq187110 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq187110
  have eq187523 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k x y) ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq187111 y x
       grind)
    | exact superpose eq187111 eq16
    | (have j1 := eq187111 y x
       grind)
    | exact resolve eq16 eq187111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187111
  have eq188127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq187523
       have i₂ := eq138939
       grind)
    | exact superpose eq138939 eq187523
    | exact resolve eq187523 eq138939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187523
  have eq188128 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq188127
  have eq188129 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq188128
  have eq921685 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (k X1 (τ X0))) ∨ (σ (k X1 (τ X0))) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15260 X1 (τ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq15260
    | (have j0 := eq15260 X1 (τ X0)
       grind)
    | exact resolve eq15260 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921686 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq921685 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq921685
    | (have j0 := eq921685 X0 X1
       grind)
    | exact resolve eq921685 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921685
  have eq921687 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) ≠ (k (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq921686 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq921686
    | (have j0 := eq921686 X0 X1
       grind)
    | exact resolve eq921686 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq921686
  have eq921688 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (σ X1) X0) ∨ (k (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq921687 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq921687
    | (have j0 := eq921687 X0 X1
       grind)
    | exact resolve eq921687 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921687
  have eq924919 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq921688 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq921688
    | exact resolve eq921688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921688
  have eq924922 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq924919 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq924919
    | (have j0 := eq924919 X0 X1
       grind)
    | exact resolve eq924919 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924919
  have eq924924 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq924922 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq924922
    | (have j0 := eq924922 X0 X1
       grind)
    | exact resolve eq924922 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq924922
  have eq924926 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq924924 x y
       have i₂ := eq188129
       grind)
    | exact superpose eq188129 eq924924
    | (have j0 := eq924924 x y
       grind)
    | exact resolve eq924924 eq188129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188129 eq924924
  have eq924932 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq924926
  have eq924934 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq924932
       have r₂ := eq138939
       grind)
    | exact resolve eq924932 eq138939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138939 eq924932
  have eq924936 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq924934
       grind)
    | exact superpose eq924934 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq924934
       grind)
    | exact resolve eq12 eq924934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq924955 : (M.op y y) = (k x y) := by grind
  clear eq924936
  have eq924990 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15260 x y
       have i₂ := eq924955
       grind)
    | exact superpose eq924955 eq15260
    | (have j0 := eq15260 x y
       grind)
    | exact resolve eq15260 eq924955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15260 eq924955
  have eq925042 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq924990
  have eq925288 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq925042
       grind)
    | exact superpose eq925042 eq16
    | exact resolve eq16 eq925042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925294 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq925288
       have i₂ := eq924934
       grind)
    | exact superpose eq924934 eq925288
    | exact resolve eq925288 eq924934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925288
  have eq925295 : (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq925294
  have eq925357 : (M.op y y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq925295
       grind)
    | exact superpose eq925295 eq10
    | exact resolve eq10 eq925295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925295
  have eq925501 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq925357
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq925357
    | exact resolve eq925357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925357
  have eq925509 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq140218
       have i₂ := eq925501
       grind)
    | exact superpose eq925501 eq140218
    | (have r₁ := eq140218
       have r₂ := eq925501
       grind)
    | exact resolve eq140218 eq925501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140218 eq925501
  have eq925761 : (M.op x x) = (k x y) := by grind
  clear eq925509
  have eq925824 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1386 x y
       have i₂ := eq925761
       grind)
    | exact superpose eq925761 eq1386
    | (have j0 := eq1386 x y
       grind)
    | exact resolve eq1386 eq925761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386 eq925761
  have eq925891 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq925824
  have eq925905 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq925891
       have r₂ := eq925042
       grind)
    | exact resolve eq925891 eq925042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925042 eq925891
  have eq925921 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq925905
       grind)
    | exact superpose eq925905 eq16
    | exact resolve eq16 eq925905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925905
  have eq925954 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq925921
       have i₂ := eq924934
       grind)
    | exact superpose eq924934 eq925921
    | exact resolve eq925921 eq924934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924934 eq925921
  have eq925955 : False := by grind
  exact eq925955

/-- `Equation3659`: `x ◇ x = (x ◇ x) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_y_pxy_x_pyx_Equation3659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq9 X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq9 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq77 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq98 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq133 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq387 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq152 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq152
    | exact resolve eq152 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq387
    | exact resolve eq387 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq398 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq394 X0
       have i₂ := eq152 X0
       grind)
    | exact superpose eq152 eq394
    | exact resolve eq394 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq423 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq633 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100 x y
       grind)
    | exact superpose eq100 eq16
    | (have j1 := eq100 x y
       grind)
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq100 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq10
    | (have j1 := eq100 X0 X1
       grind)
    | exact resolve eq10 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq666 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq648 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq648
    | (have j0 := eq648 X0 X1
       grind)
    | exact resolve eq648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq2457 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq152 X1
       have i₂ := eq423 X0 X1
       grind)
    | (have i₁ := eq152 X0
       have i₂ := eq423 (M.op X0 X0) X1
       grind)
    | exact superpose eq423 eq152
    | (have j1 := eq423 X0 X1
       grind)
    | exact resolve eq152 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq423
  have eq2472 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq4937 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq666 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq666 X0 X1
       grind)
    | exact superpose eq666 eq10
    | (have j1 := eq666 X0 X1
       grind)
    | exact resolve eq10 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq4990 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4937 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4937
    | (have j0 := eq4937 X0 X1
       grind)
    | exact resolve eq4937 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4937
  have eq5134 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq133
    | (have j0 := eq133 X1 (σ X0)
       grind)
    | (have r₁ := eq133 X0 (σ X0)
       have r₂ := eq42 X0
       grind)
    | exact resolve eq133 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq5180 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5134 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5134
    | (have j0 := eq5134 X0 X1
       grind)
    | exact resolve eq5134 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5134
  have eq5225 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq5565 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5225 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5225
    | (have j0 := eq5225 X0 X1
       grind)
    | exact resolve eq5225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5225
  have eq6429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq633
       have i₂ := eq2472 x y
       grind)
    | exact superpose eq2472 eq633
    | (have j1 := eq2472 x y
       grind)
    | exact resolve eq633 eq2472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq2472
  have eq6432 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq6429
  have eq252560 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4990 x y
       grind)
    | exact superpose eq4990 eq16
    | (have j1 := eq4990 x y
       grind)
    | exact resolve eq16 eq4990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4990
  have eq252623 : (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq5565 x y
       grind)
    | (have r₁ := eq252560
       have r₂ := eq5565 x y
       grind)
    | exact resolve eq252560 eq5565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5565 eq252560
  have eq253330 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq5180 y X0
       have i₂ := eq252623
       grind)
    | exact superpose eq252623 eq5180
    | (have j0 := eq5180 X0 x
       grind)
    | exact resolve eq5180 eq252623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5180 eq252623
  have eq905972 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq6432
       grind)
    | exact superpose eq6432 eq10
    | exact resolve eq10 eq6432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6432
  have eq905974 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq905972
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq905972
    | exact resolve eq905972 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905972
  have eq905975 : (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq905974
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq905974
       have r₂ := eq12 y x
       grind)
    | exact resolve eq905974 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905974
  have eq911999 : (M.op (σ x) (σ x)) = (σ (M.op (M.op y y) (M.op y y))) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq42 (M.op y y)
       have i₂ := eq905975
       grind)
    | exact superpose eq905975 eq42
    | exact resolve eq42 eq905975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905975
  have eq912016 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq911999
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq911999
    | exact resolve eq911999 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911999
  have eq912030 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq912016
       have i₂ := eq42 x
       grind)
    | exact superpose eq42 eq912016
    | exact resolve eq912016 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq912016
  have eq917986 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq912030
       grind)
    | exact superpose eq912030 eq10
    | exact resolve eq10 eq912030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912030
  have eq918023 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq917986
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq917986
    | exact resolve eq917986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917986
  have eq918025 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq918023
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq918023
       have r₂ := eq12 y x
       grind)
    | exact resolve eq918023 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918023
  have eq2149245 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq253330 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253330
  have eq2149246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2149245
       have i₂ := eq918025
       grind)
    | exact superpose eq918025 eq2149245
    | exact resolve eq2149245 eq918025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918025 eq2149245
  have eq2149248 : x = (M.op y y) := by
    first
    | (have r₁ := eq2149246
       have r₂ := eq16
       grind)
    | exact resolve eq2149246 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149246
  have eq2149606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq398 y
       have i₂ := eq2149248
       grind)
    | exact superpose eq2149248 eq398
    | exact resolve eq398 eq2149248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq2149248
  have eq2150228 : False := by grind
  exact eq2150228

/-- `Equation378`: `x ◇ y = (x ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation378 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law378 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law378.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq47 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq49 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq47 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq47 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq51 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 (M.op X0 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq49 X1 X0
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq49 (k X1 X0) X1
       grind)
    | (have r₁ := eq51 X0 X0
       have r₂ := eq49 X0 (k X0 X0)
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq49 X0 X1
       grind)
    | exact resolve eq51 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq49 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq52 (σ X0) (σ X1)
       grind)
    | exact superpose eq52 eq15
    | (have j1 := eq52 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq52 X0 (τ X1)
       grind)
    | exact superpose eq52 eq19
    | (have j1 := eq52 X0 (τ X1)
       grind)
    | exact resolve eq19 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq66
    | exact resolve eq66 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq55 (τ X0) X1
       grind)
    | exact superpose eq55 eq20
    | (have j1 := eq55 (τ X0) X1
       grind)
    | exact resolve eq20 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq80 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq83 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq143 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80 X1 (M.op X0 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq80
    | (have j0 := eq80 X1 X0
       grind)
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq174 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq187 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq9
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq193 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq191 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq191
    | (have j0 := eq191 X0
       grind)
    | exact resolve eq191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq446 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq174 (σ X1) X0
       grind)
    | exact superpose eq174 eq32
    | (have j1 := eq174 (σ X1) X0
       grind)
    | exact resolve eq32 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq466 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq446 X0 X1
       have i₂ := eq71 X1
       grind)
    | exact superpose eq71 eq446
    | (have j0 := eq446 X0 X1
       grind)
    | exact resolve eq446 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq662 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq143 (σ X0) (σ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq143
    | exact resolve eq143 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq143
  have eq669 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) ≠ (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq662 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq662
    | (have j0 := eq662 X0
       grind)
    | exact resolve eq662 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq674 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq669 X0
       have j1 := eq193 X0
       grind)
    | (have r₁ := eq669 X0
       have r₂ := eq193 X0
       grind)
    | exact resolve eq669 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq669
  have eq773 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq674 X0
       grind)
    | exact superpose eq674 eq10
    | exact resolve eq10 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (k X0 (M.op X0 X0))
       have i₂ := eq674 X0
       grind)
    | exact superpose eq674 eq15
    | exact resolve eq15 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (k X1 (k X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq775
    | exact resolve eq775 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq807 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq773 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq773
    | exact resolve eq773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq957 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62
    | exact resolve eq62 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1002 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq957 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq957
    | (have j0 := eq957 X0 X1
       grind)
    | exact resolve eq957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1067 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1119 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1067 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1067
    | (have j0 := eq1067 X0 X1
       grind)
    | exact resolve eq1067 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1317 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75 y x
       grind)
    | exact superpose eq75 eq16
    | (have j1 := eq75 y x
       grind)
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1788 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op (k X0 (M.op X0 X0)) X1)) ∨ (k X0 (M.op X0 X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq805 X0 X1
       have i₂ := eq174 X1 (k X0 (M.op X0 X0))
       grind)
    | exact superpose eq174 eq805
    | (have j1 := eq174 X1 (k X0 (M.op X0 X0))
       grind)
    | exact resolve eq805 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq805
  have eq1842 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X0 (M.op X0 X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1788 X0 X1
       have i₂ := eq807 X0
       grind)
    | exact superpose eq807 eq1788
    | (have j0 := eq1788 X0 X1
       grind)
    | exact resolve eq1788 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788
  have eq1864 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1842 X0 X1
       have i₂ := eq807 X0
       grind)
    | exact superpose eq807 eq1842
    | (have j0 := eq1842 X0 X1
       grind)
    | exact resolve eq1842 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq1842
  have eq1909 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61 x y
       grind)
    | exact superpose eq61 eq16
    | (have j1 := eq61 x y
       grind)
    | exact resolve eq16 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1931 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq11675 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1931 (τ X1) (τ X0)
       have i₂ := eq83 X1 X0
       grind)
    | exact superpose eq83 eq1931
    | (have j0 := eq1931 (τ X1) (τ X0)
       grind)
    | exact resolve eq1931 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq11717 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11675 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11675
    | (have j0 := eq11675 X0 X1
       grind)
    | exact resolve eq11675 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11675
  have eq11728 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11717 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11717
    | (have j0 := eq11717 X0 X1
       grind)
    | exact resolve eq11717 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11717
  have eq11732 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11728 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11728
    | (have j0 := eq11728 X0 X1
       grind)
    | exact resolve eq11728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11728
  have eq11735 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11732 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11732
    | (have j0 := eq11732 X0 X1
       grind)
    | exact resolve eq11732 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11732
  have eq23014 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1317
       have i₂ := eq1002 y x
       grind)
    | exact superpose eq1002 eq1317
    | (have j1 := eq1002 y x
       grind)
    | (have r₁ := eq1317
       have r₂ := eq1002 y x
       grind)
    | exact resolve eq1317 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23015 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1317
       have i₂ := eq1119 x y
       grind)
    | exact superpose eq1119 eq1317
    | (have j1 := eq1119 x y
       grind)
    | (have r₁ := eq1317
       have r₂ := eq1119 x y
       grind)
    | exact resolve eq1317 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq23016 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1317
       have i₂ := eq1864 x y
       grind)
    | exact superpose eq1864 eq1317
    | (have j1 := eq1864 x y
       grind)
    | (have r₁ := eq1317
       have r₂ := eq1864 x y
       grind)
    | exact resolve eq1317 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317 eq1864
  have eq23019 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq23016
  have eq23020 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq23015
  have eq23021 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq23014
  have eq23034 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq23020
       grind)
    | exact superpose eq23020 eq10
    | exact resolve eq10 eq23020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23020
  have eq23127 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq23034
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq23034
    | exact resolve eq23034 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23034
  have eq23132 : y = (k y x) := by
    first
    | (have j1 := eq80 y x
       grind)
    | (have r₁ := eq23127
       have r₂ := eq80 y x
       grind)
    | exact resolve eq23127 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq23127
  have eq23394 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 x y
       have i₂ := eq23132
       grind)
    | exact superpose eq23132 eq52
    | (have j0 := eq52 x y
       grind)
    | exact resolve eq52 eq23132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq23401 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1931 x y
       have i₂ := eq23132
       grind)
    | exact superpose eq23132 eq1931
    | (have j0 := eq1931 x y
       grind)
    | exact resolve eq1931 eq23132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931 eq23132
  have eq24708 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq23394
       grind)
    | exact superpose eq23394 eq9
    | exact resolve eq9 eq23394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23394
  have eq24725 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1909
       have i₂ := eq1002 y x
       grind)
    | exact superpose eq1002 eq1909
    | (have j1 := eq1002 (σ y) (σ x)
       grind)
    | (have r₁ := eq1909
       have r₂ := eq1002 y x
       grind)
    | exact resolve eq1909 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002 eq1909
  have eq24733 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24725
  have eq24994 : (σ y) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq674 y
       have i₂ := eq24708
       grind)
    | exact superpose eq24708 eq674
    | exact resolve eq674 eq24708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq24708
  have eq25015 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24994
       have i₂ := eq58 y
       grind)
    | exact superpose eq58 eq24994
    | exact resolve eq24994 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq24994
  have eq28751 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24733
       grind)
    | exact superpose eq24733 eq16
    | exact resolve eq16 eq24733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28760 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq466 (σ x) y
       have i₂ := eq24733
       grind)
    | exact superpose eq24733 eq466
    | (have j0 := eq466 (σ x) y
       grind)
    | exact resolve eq466 eq24733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466 eq24733
  have eq28770 : x = (k y x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28760
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28760
    | exact resolve eq28760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28760
  have eq28783 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq11735 y x
       grind)
    | (have r₁ := eq28770
       have r₂ := eq11735 y x
       grind)
    | exact resolve eq28770 eq11735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11735 eq28770
  have eq29194 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28751
       have i₂ := eq23021
       grind)
    | exact superpose eq23021 eq28751
    | exact resolve eq28751 eq23021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23021 eq28751
  have eq29199 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq29194
  have eq30071 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25015
       have i₂ := eq28783
       grind)
    | exact superpose eq28783 eq25015
    | exact resolve eq25015 eq28783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25015 eq28783
  have eq30155 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq30071
  have eq30184 : x = (M.op x y) := by
    first
    | (have r₁ := eq30155
       have r₂ := eq29199
       grind)
    | exact resolve eq30155 eq29199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29199 eq30155
  have eq30731 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23019
       have i₂ := eq30184
       grind)
    | exact superpose eq30184 eq23019
    | exact resolve eq23019 eq30184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23019
  have eq31801 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq187 y
       have i₂ := eq30731
       grind)
    | exact superpose eq30731 eq187
    | exact resolve eq187 eq30731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq30731
  have eq31834 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31801
       have r₂ := eq23401
       grind)
    | exact resolve eq31801 eq23401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23401 eq31801
  have eq32139 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31834
       grind)
    | exact superpose eq31834 eq16
    | exact resolve eq16 eq31834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31834
  have eq32166 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq32139
       have i₂ := eq30184
       grind)
    | exact superpose eq30184 eq32139
    | exact resolve eq32139 eq30184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30184 eq32139
  have eq32167 : False := by grind
  exact eq32167

/-- `Equation378`: `x ◇ y = (x ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pxy_Equation378 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law378 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law378.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq53 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq46
  have eq729 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq10
    | (have j1 := eq54 X1 X0
       grind)
    | exact resolve eq10 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq4478 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq411 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq4480 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478
  have eq4481 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4480 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4480
  have eq4628 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4481 (σ X0)
       grind)
    | exact superpose eq4481 eq15
    | exact resolve eq15 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4647 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4628 X0
       have i₂ := eq4481 X0
       grind)
    | exact superpose eq4481 eq4628
    | exact resolve eq4628 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4481 eq4628
  have eq5270 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq5300 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq4647 X0
       grind)
    | exact superpose eq4647 eq9
    | exact resolve eq9 eq4647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5331 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5270 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq5270
    | exact resolve eq5270 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5270
  have eq5350 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5331
  have eq7709 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq8063 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7709 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7709
    | (have j0 := eq7709 X0 X1
       grind)
    | exact resolve eq7709 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7709
  have eq36207 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq729 X1 X0
       grind)
    | exact superpose eq729 eq10
    | (have j1 := eq729 X1 X0
       grind)
    | exact resolve eq10 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq36619 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36207 X0 X1
       have i₂ := eq4647 X0
       grind)
    | exact superpose eq4647 eq36207
    | (have j0 := eq36207 X0 X1
       grind)
    | exact resolve eq36207 eq4647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36207
  have eq37216 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36619 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq36619
    | (have j0 := eq36619 X0 X1
       grind)
    | exact resolve eq36619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36619
  have eq37734 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37216 X0 X1
       have i₂ := eq4647 X1
       grind)
    | exact superpose eq4647 eq37216
    | (have j0 := eq37216 X0 X1
       grind)
    | exact resolve eq37216 eq4647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4647 eq37216
  have eq38097 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37734 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq37734
    | (have j0 := eq37734 X0 X1
       grind)
    | exact resolve eq37734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37734
  have eq148349 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38097 x y
       grind)
    | exact superpose eq38097 eq16
    | (have j1 := eq38097 x y
       grind)
    | exact resolve eq16 eq38097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38097
  have eq148395 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq8063 x y
       grind)
    | (have r₁ := eq148349
       have r₂ := eq8063 y x
       grind)
    | exact resolve eq148349 eq8063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8063 eq148349
  have eq150688 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5300 y
       have i₂ := eq148395
       grind)
    | exact superpose eq148395 eq5300
    | exact resolve eq5300 eq148395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5300
  have eq150719 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq148395
       grind)
    | exact superpose eq148395 eq9
    | exact resolve eq9 eq148395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148395
  have eq161131 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq150688
       grind)
    | exact superpose eq150688 eq16
    | exact resolve eq16 eq150688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150688
  have eq162360 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq161131
       have i₂ := eq150719
       grind)
    | exact superpose eq150719 eq161131
    | exact resolve eq161131 eq150719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150719 eq161131
  have eq162361 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by grind
  clear eq162360
  have eq162362 : y = (M.op x x) := by grind
  clear eq162361
  have eq163650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5350 x
       have i₂ := eq162362
       grind)
    | exact superpose eq162362 eq5350
    | exact resolve eq5350 eq162362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350 eq162362
  have eq163738 : False := by grind
  exact eq163738

/-- `Equation4040`: `x ◇ y = (z ◇ (w ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pxy_Equation4040 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4040 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4040.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) X1) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq36 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq115 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq92 X0 (τ X1)
       grind)
    | exact superpose eq92 eq20
    | (have j1 := eq92 X0 (τ X1)
       grind)
    | exact resolve eq20 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq117 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq15
    | (have j1 := eq92 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq92
  have eq148 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq126 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq149 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq148 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq190 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq149 (σ X0)
       grind)
    | exact superpose eq149 eq15
    | exact resolve eq15 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq149 (τ X0)
       grind)
    | exact superpose eq149 eq38
    | exact resolve eq38 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq195 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq192 X0
       have i₂ := eq149 X0
       grind)
    | exact superpose eq149 eq192
    | exact resolve eq192 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq197 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq190 X0
       have i₂ := eq149 X0
       grind)
    | exact superpose eq149 eq190
    | exact resolve eq190 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq190
  have eq290 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = (M.op (M.op X2 (τ (M.op X0 X0))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2 (τ X0)
       have i₂ := eq195 X0
       grind)
    | exact superpose eq195 eq9
    | exact resolve eq9 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4756 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq115
    | exact resolve eq115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq4920 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4756 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4756
    | (have j0 := eq4756 X0 X1
       grind)
    | exact resolve eq4756 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4756
  have eq6672 : ∀ X0 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (k (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq290 X0 (τ (M.op X0 X0)) (τ (M.op X0 X0))
       grind)
    | exact superpose eq290 eq36
    | exact resolve eq36 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq290
  have eq6743 : ∀ X0 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (k (σ (τ (M.op (M.op X0 X0) (M.op X0 X0)))) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6672 X0
       have i₂ := eq195 (M.op X0 X0)
       grind)
    | exact superpose eq195 eq6672
    | exact resolve eq6672 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq6672
  have eq6788 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq6743 X0
       have i₂ := eq11 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq6743
    | exact resolve eq6743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6743
  have eq6826 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq6788
  have eq6862 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq6826 X0
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq6826
    | exact resolve eq6826 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6826
  have eq6984 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq6862 (σ X0)
       have i₂ := eq197 X0
       grind)
    | exact superpose eq197 eq6862
    | exact resolve eq6862 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6862
  have eq7057 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ X0)) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6984 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6984
    | exact resolve eq6984 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6984
  have eq7083 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7057 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7057
    | exact resolve eq7057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7057
  have eq7277 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq117 X0 X1
       grind)
    | exact superpose eq117 eq10
    | (have j1 := eq117 X0 X1
       grind)
    | exact resolve eq10 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq7443 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7277 X0 X1
       have i₂ := eq197 X0
       grind)
    | exact superpose eq197 eq7277
    | (have j0 := eq7277 X0 X1
       grind)
    | exact resolve eq7277 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq7277
  have eq7588 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7443 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq7443
    | (have j0 := eq7443 X0 X1
       grind)
    | exact resolve eq7443 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7443
  have eq9371 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7588 x y
       grind)
    | exact superpose eq7588 eq16
    | (have j1 := eq7588 x y
       grind)
    | exact resolve eq16 eq7588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7588
  have eq9486 : y = (M.op x x) := by
    first
    | (have j1 := eq4920 y x
       grind)
    | (have r₁ := eq9371
       have r₂ := eq4920 y x
       grind)
    | exact resolve eq9371 eq4920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4920 eq9371
  have eq10074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7083 x
       have i₂ := eq9486
       grind)
    | exact superpose eq9486 eq7083
    | exact resolve eq7083 eq9486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7083 eq9486
  have eq10098 : False := by grind
  exact eq10098

/-- `Equation4080`: `x ◇ x = ((y ◇ x) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation4080 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4080 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4080.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X0) X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x X0)
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq63 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq61 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq61 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq61 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq74 (σ X0)
       grind)
    | exact superpose eq74 eq15
    | exact resolve eq15 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq84
    | exact resolve eq84 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq84
  have eq214 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq215 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq214 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq267 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | (have j0 := eq56 X1 X1
       grind)
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq378 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 X1
       have i₂ := eq91 X1
       grind)
    | exact superpose eq91 eq267
    | (have j0 := eq267 (σ X1) X1
       grind)
    | exact resolve eq267 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq422 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq378
    | (have j0 := eq378 X0 X1
       grind)
    | exact resolve eq378 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq378
  have eq453 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq422 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq422 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X1
       have r₂ := eq12 (σ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq422 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq422 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq498 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq25
    | exact resolve eq25 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1220 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq453 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq453 (σ X0) X1
       grind)
    | exact superpose eq453 eq10
    | (have j1 := eq453 X0 X1
       grind)
    | exact resolve eq10 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq2308 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1220 (σ X0) X1
       grind)
    | exact superpose eq1220 eq15
    | (have j1 := eq1220 (σ X0) X1
       grind)
    | exact resolve eq15 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq2343 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2308 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2308
    | (have j0 := eq2308 X0 X1
       grind)
    | exact resolve eq2308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq4784 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2343 x y
       grind)
    | exact superpose eq2343 eq16
    | (have j1 := eq2343 x y
       grind)
    | exact resolve eq16 eq2343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq5001 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4784
       have i₂ := eq215 y x
       grind)
    | exact superpose eq215 eq4784
    | (have j1 := eq215 y x
       grind)
    | exact resolve eq4784 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq4784
  have eq5007 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq5001
  have eq5008 : x = (M.op y y) := by grind
  clear eq5007
  have eq5447 : x = (M.op x y) := by
    first
    | (have i₁ := eq25 y
       have i₂ := eq5008
       grind)
    | exact superpose eq5008 eq25
    | exact resolve eq25 eq5008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq5453 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq498 y
       have i₂ := eq5008
       grind)
    | exact superpose eq5008 eq498
    | exact resolve eq498 eq5008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq5008
  have eq6395 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5453
       grind)
    | exact superpose eq5453 eq16
    | exact resolve eq16 eq5453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5453
  have eq6416 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6395
       have i₂ := eq5447
       grind)
    | exact superpose eq5447 eq6395
    | exact resolve eq6395 eq5447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447 eq6395
  have eq6417 : False := by grind
  exact eq6417

/-- `Equation4080`: `x ◇ x = ((y ◇ x) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_pxx_pxy_Equation4080 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4080 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4080.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X0) X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x X0)
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq49 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq44
  have eq706 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq7124 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq248 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq7126 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7124 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7124
  have eq7127 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7126 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7126
  have eq7274 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7127 (σ X0)
       grind)
    | exact superpose eq7127 eq15
    | exact resolve eq15 eq7127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7293 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7274 X0
       have i₂ := eq7127 X0
       grind)
    | exact superpose eq7127 eq7274
    | exact resolve eq7274 eq7127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7127 eq7274
  have eq8407 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq8409 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq7293 X0
       grind)
    | exact superpose eq7293 eq26
    | exact resolve eq26 eq7293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8465 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8407 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq8407
    | exact resolve eq8407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8407
  have eq8502 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq8465
  have eq10995 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq11458 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10995 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10995
    | (have j0 := eq10995 X0 X1
       grind)
    | exact resolve eq10995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10995
  have eq33854 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq706 X1 X0
       grind)
    | exact superpose eq706 eq10
    | (have j1 := eq706 X1 X0
       grind)
    | exact resolve eq10 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq34261 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33854 X0 X1
       have i₂ := eq7293 X0
       grind)
    | exact superpose eq7293 eq33854
    | (have j0 := eq33854 X0 X1
       grind)
    | exact resolve eq33854 eq7293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33854
  have eq34793 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34261 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq34261
    | (have j0 := eq34261 X0 X1
       grind)
    | exact resolve eq34261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34261
  have eq35241 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34793 X0 X1
       have i₂ := eq7293 X1
       grind)
    | exact superpose eq7293 eq34793
    | (have j0 := eq34793 X0 X1
       grind)
    | exact resolve eq34793 eq7293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7293 eq34793
  have eq35551 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35241 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq35241
    | (have j0 := eq35241 X0 X1
       grind)
    | exact resolve eq35241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35241
  have eq126223 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35551 x y
       grind)
    | exact superpose eq35551 eq16
    | (have j1 := eq35551 x y
       grind)
    | exact resolve eq16 eq35551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35551
  have eq126336 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq11458 x y
       grind)
    | (have r₁ := eq126223
       have r₂ := eq11458 y x
       grind)
    | exact resolve eq126223 eq11458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11458 eq126223
  have eq126670 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26 y
       have i₂ := eq126336
       grind)
    | exact superpose eq126336 eq26
    | exact resolve eq26 eq126336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq126685 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8409 y
       have i₂ := eq126336
       grind)
    | exact superpose eq126336 eq8409
    | exact resolve eq8409 eq126336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8409 eq126336
  have eq132316 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq126685
       grind)
    | exact superpose eq126685 eq16
    | exact resolve eq16 eq126685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126685
  have eq132874 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq132316
       have i₂ := eq126670
       grind)
    | exact superpose eq126670 eq132316
    | exact resolve eq132316 eq126670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126670 eq132316
  have eq132875 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by grind
  clear eq132874
  have eq132876 : y = (M.op x x) := by grind
  clear eq132875
  have eq133284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8502 x
       have i₂ := eq132876
       grind)
    | exact superpose eq132876 eq8502
    | exact resolve eq8502 eq132876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8502 eq132876
  have eq133389 : False := by grind
  exact eq133389
