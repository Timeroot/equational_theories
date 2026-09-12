import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1052`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxx_pyx_pxy_Equation1052 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1052 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1052.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X1)) = X0 := by
    intro X0 X1 X2
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
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq176 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq176 X0 (M.op X0 X0)
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1041 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1105 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1105 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1105 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1154 : ∀ X0 X1 : G, (M.op X1 (k (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq1115 (M.op X0 X0)
       grind)
    | exact superpose eq1115 eq199
    | exact resolve eq199 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq1155 : ∀ X0 X1 : G, (M.op X1 (k (k X0 X0) (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1154 X0 X1
       have i₂ := eq1115 X0
       grind)
    | exact superpose eq1115 eq1154
    | exact resolve eq1154 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1677 : ∀ X0 X1 : G, (M.op X1 (k (σ (k X0 X0)) (σ (k X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1155 (σ X1) X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq1155
    | exact resolve eq1155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1734 : ∀ X0 X1 : G, (M.op X1 (σ (k (k X0 X0) (k X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1677 X0 X1
       have i₂ := eq10 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10 eq1677
    | exact resolve eq1677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq4147 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1041
       grind)
    | exact superpose eq1041 eq40
    | exact resolve eq40 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq4148 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4147
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4147
    | exact resolve eq4147 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147
  have eq4150 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq4148
    | exact resolve eq4148 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148
  have eq4152 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq4150
       have i₂ := eq1115 y
       grind)
    | exact superpose eq1115 eq4150
    | exact resolve eq4150 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4150
  have eq92406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4152 eq1042
    | exact resolve eq1042 eq4152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92415 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq92406
       have r₂ := eq27
       grind)
    | exact resolve eq92406 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92406
  have eq92422 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq92415
       have i₂ := eq1115 sF3
       grind)
    | exact superpose eq1115 eq92415
    | exact resolve eq92415 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92415
  have eq92427 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq92422 eq12
    | (have j0 := eq12 x (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq92422
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq92422
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq92422
       grind)
    | exact resolve eq12 eq92422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92422
  have eq92452 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq92427
       have r₂ := eq26
       grind)
    | exact resolve eq92427 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92427
  have eq92458 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq92452
       have i₂ := eq1115 sF3
       grind)
    | exact superpose eq1115 eq92452
    | exact resolve eq92452 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92452
  have eq92459 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq92458
  have eq92464 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4152 eq92459
    | exact resolve eq92459 eq4152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4152 eq92459
  have eq92466 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq92464
       have r₂ := eq27
       grind)
    | exact resolve eq92464 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92464
  have eq92471 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq92466 eq152
    | exact resolve eq152 eq92466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92466
  have eq92684 : y = (k y y) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq31 eq92471
    | exact resolve eq92471 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92471
  have eq92685 : (M.op x y) = (M.op y x) ∨ y = (k y y) := by grind
  clear eq92684
  have eq92789 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq92685
       grind)
    | exact superpose eq92685 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq92685
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq92685
       grind)
    | exact resolve eq12 eq92685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92685
  have eq92814 : y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have r₁ := eq92789
       have r₂ := eq18
       grind)
    | exact resolve eq92789 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92789
  have eq92820 : y = (k y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq92814
       have i₂ := eq1115 y
       grind)
    | exact superpose eq1115 eq92814
    | exact resolve eq92814 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92814
  have eq92821 : (M.op x y) = (k x y) ∨ y = (k y y) := by grind
  clear eq92820
  have eq92830 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq92821
       grind)
    | exact superpose eq92821 eq40
    | exact resolve eq40 eq92821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92821
  have eq92832 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq92830
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq92830
    | exact resolve eq92830 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92830
  have eq92836 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq92832
    | exact resolve eq92832 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92832
  have eq92841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq92836 eq1042
    | exact resolve eq1042 eq92836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq92850 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq92841
       have r₂ := eq27
       grind)
    | exact resolve eq92841 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92841
  have eq92857 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq92850
       have i₂ := eq1115 sF3
       grind)
    | exact superpose eq1115 eq92850
    | exact resolve eq92850 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92850
  have eq93336 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq92857 eq12
    | (have j0 := eq12 x (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq92857
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq92857
       grind)
    | exact resolve eq12 eq92857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92857
  have eq93361 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq93336
       have r₂ := eq26
       grind)
    | exact resolve eq93336 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93336
  have eq93367 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq93361
       have i₂ := eq1115 sF3
       grind)
    | exact superpose eq1115 eq93361
    | exact resolve eq93361 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq93361
  have eq93368 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by grind
  clear eq93367
  have eq93373 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq92836 eq93368
    | exact resolve eq93368 eq92836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92836 eq93368
  have eq93375 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq93373
       have r₂ := eq27
       grind)
    | exact resolve eq93373 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93373
  have eq93380 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) := by
    first
    | exact superpose eq93375 eq152
    | exact resolve eq152 eq93375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq93375
  have eq93593 : y = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq93380
    | exact resolve eq93380 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq93380
  have eq93594 : y = (k y y) := by grind
  clear eq93593
  have eq93698 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq93594
       grind)
    | exact superpose eq93594 eq40
    | exact resolve eq40 eq93594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93703 : ∀ X0 : G, (M.op X0 (k y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1155 y x
       have i₂ := eq93594
       grind)
    | exact superpose eq93594 eq1155
    | exact resolve eq1155 eq93594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq93726 : ∀ X0 : G, (M.op X0 (σ (k y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1734 y x
       have i₂ := eq93594
       grind)
    | exact superpose eq93594 eq1734
    | exact resolve eq1734 eq93594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq93888 : ∀ X0 : G, (M.op X0 (k (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq93726 X0
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq93726
    | exact resolve eq93726 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq93726
  have eq93908 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq93703 X0
       have i₂ := eq93594
       grind)
    | exact superpose eq93594 eq93703
    | exact resolve eq93703 eq93594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93594 eq93703
  have eq93911 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq93698
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq93698
    | exact resolve eq93698 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93698
  have eq93987 : ∀ X0 : G, (M.op X0 (k (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq93888 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq93888
    | (have j0 := eq93888 X0
       grind)
    | exact resolve eq93888 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq93888
  have eq94057 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq93911 eq93987
    | exact resolve eq93987 eq93911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93911 eq93987
  have eq94249 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq93908 x
       grind)
    | exact superpose eq93908 eq18
    | (have j1 := eq93908 x
       grind)
    | exact resolve eq18 eq93908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq93908
  have eq94501 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq94249
       grind)
    | exact superpose eq94249 eq22
    | exact resolve eq22 eq94249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq94249
  have eq94678 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq94501 eq20
    | exact resolve eq20 eq94501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq94501
  have eq95948 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq94057 eq26
    | (have j1 := eq94057 (σ x)
       grind)
    | exact resolve eq26 eq94057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq94057
  have eq96200 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq95948 eq27
    | exact resolve eq27 eq95948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq95948
  have eq96293 : False := by grind
  exact eq96293

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_x_pxy_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 : G, (M.op X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq14 X0 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq76 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq93 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq94
    | (have j0 := eq94 (σ X0) (σ X1)
       grind)
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq44
    | (have j1 := eq94 x y
       grind)
    | exact resolve eq44 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120 eq94
    | (have j0 := eq94 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq140 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq157 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq175 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq141 eq16
    | exact resolve eq16 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq226 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq521 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X2))) ≠ X0 ∨ (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) = (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       have i₂ := eq53 X1 X0 X2
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X2 (M.op X0 X2))) (M.op X0 (M.op X2 (M.op X0 X2)))
       have r₂ := eq53 X0 (M.op X0 (M.op X2 (M.op X0 X2))) X2
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq77
    | (have r₁ := eq77
       have r₂ := eq129
       grind)
    | exact resolve eq77 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq129
  have eq586 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq585
  have eq589 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq586 eq120
    | exact resolve eq120 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq592 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq589
  have eq605 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq592 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq592
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq592
       grind)
    | exact resolve eq13 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq607 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq605
  have eq613 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq607
    | exact resolve eq607 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq613 eq120
    | exact resolve eq120 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq613
  have eq721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq718
  have eq725 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq721
       have r₂ := eq27
       grind)
    | exact resolve eq721 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq728 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq725 eq28
    | exact resolve eq28 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq725
  have eq776 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq728
    | exact resolve eq728 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq728
  have eq884 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq776 eq20
    | exact resolve eq20 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq885 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq776 eq45
    | exact resolve eq45 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq889 : y ≠ y ∨ x = (M.op y x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq776 eq76
    | (have r₁ := eq76
       have r₂ := eq776
       grind)
    | exact resolve eq76 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq893 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq894 : x = (k x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq889
  have eq900 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq885
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq885
    | exact resolve eq885 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq901 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq884
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq884
    | exact resolve eq884 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq905 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq901 eq40
    | exact resolve eq40 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq909 : (k y y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq901 eq88
    | exact resolve eq88 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq910 : (k y (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq901 eq93
    | exact resolve eq93 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq913 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq901 eq157
    | exact resolve eq157 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq932 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq175 eq913
    | exact resolve eq913 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq933 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq175 eq910
    | exact resolve eq910 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq934 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq175 eq909
    | exact resolve eq909 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq937 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq905
    | exact resolve eq905 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq905
  have eq979 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq98 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq12 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq980 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq98 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq13 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq982 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq983 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq980 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq980 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | exact resolve eq980 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq984 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq979 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq979 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq979 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq979 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq987 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq983 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq983
    | (have j0 := eq983 X0 X1
       grind)
    | exact resolve eq983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq988 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq984 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq984
    | (have j0 := eq984 X0 X1
       grind)
    | exact resolve eq984 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1198 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq900 eq94
    | (have j0 := eq94 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq1199 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1198
    | exact resolve eq1198 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1202 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1199
    | exact resolve eq1199 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1287 : (k y (M.op x y)) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq933 eq932
    | exact resolve eq932 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932 eq933
  have eq1293 : (k y (M.op x y)) = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq1287
  have eq1296 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq776 eq220
    | exact resolve eq220 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2017 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1202 eq62
    | exact resolve eq62 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq3403 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq937 eq34
    | exact resolve eq34 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3410 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (σ (k X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq937 eq16
    | exact resolve eq16 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3432 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3410 X0
       have i₂ := eq16 (k X0 y)
       grind)
    | exact superpose eq16 eq3410
    | exact resolve eq3410 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410
  have eq3438 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq3403
    | (have j0 := eq3403 X0
       grind)
    | exact resolve eq3403 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq3445 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3438 X0
       have i₂ := eq34 X0 y
       grind)
    | exact superpose eq34 eq3438
    | exact resolve eq3438 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3438
  have eq3449 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3445 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3445
    | (have j0 := eq3445 X0
       grind)
    | exact resolve eq3445 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445
  have eq4772 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2017 eq937
    | exact resolve eq937 eq2017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937 eq2017
  have eq4776 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4772
  have eq4781 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4776
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq4776
    | exact resolve eq4776 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4776
  have eq4784 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4781
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq4781
    | exact resolve eq4781 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq4781
  have eq4786 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq901 eq4784
    | exact resolve eq4784 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq4806 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq4786
  have eq4807 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4806
       have r₂ := eq27
       grind)
    | exact resolve eq4806 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4806
  have eq4873 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4807 eq62
    | exact resolve eq62 eq4807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq4807
  have eq4885 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4873 eq3432
    | exact resolve eq3432 eq4873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432 eq4873
  have eq4891 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq4885
  have eq7484 : (σ y) ≠ (σ (k y (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1293 eq982
    | (have j0 := eq982 (M.op x y) y
       grind)
    | exact resolve eq982 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7656 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75 eq7484
    | exact resolve eq7484 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7484
  have eq7729 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7656
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7656
    | exact resolve eq7656 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7656
  have eq7778 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7729
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7729
    | exact resolve eq7729 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7729
  have eq7796 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq7778
    | exact resolve eq7778 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7778
  have eq12153 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq141 eq987
    | exact resolve eq987 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq12194 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq12153
    | exact resolve eq12153 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12153
  have eq12299 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq12194
    | exact resolve eq12194 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12194
  have eq15650 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4891
       have i₂ := eq894
       grind)
    | exact superpose eq894 eq4891
    | exact resolve eq4891 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq4891
  have eq15657 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq15650
  have eq15679 : x ≠ x ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq15657
       grind)
    | exact superpose eq15657 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15657
       grind)
    | exact resolve eq13 eq15657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15657
  have eq15693 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq15679
  have eq15696 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq15693
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15693
    | exact resolve eq15693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15693
  have eq16338 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq982 x y
       have i₂ := eq15696
       grind)
    | exact superpose eq15696 eq982
    | (have j0 := eq982 x y
       grind)
    | exact resolve eq982 eq15696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15696
  have eq16346 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq16338
    | exact resolve eq16338 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16338
  have eq16349 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16346
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16346
    | exact resolve eq16346 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16346
  have eq16351 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq16349
       have r₂ := eq901
       grind)
    | exact resolve eq16349 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16349
  have eq16353 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16351
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16351
    | exact resolve eq16351 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16351
  have eq16355 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16353
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16353
    | exact resolve eq16353 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16353
  have eq16357 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16355
    | exact resolve eq16355 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16355
  have eq16359 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16357 eq15
    | exact resolve eq15 eq16357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16357
  have eq16376 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16359
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16359
    | exact resolve eq16359 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16359
  have eq17050 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16376 eq27
    | exact resolve eq27 eq16376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16376
  have eq17072 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17050
       have r₂ := eq901
       grind)
    | exact resolve eq17050 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17050
  have eq17080 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17072 eq226
    | exact resolve eq226 eq17072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq17072
  have eq20207 : (σ y) ≠ (σ (k y (M.op x y))) ∨ (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1293 eq988
    | (have j0 := eq988 (M.op x y) y
       grind)
    | exact resolve eq988 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq1293
  have eq20413 : (σ y) ≠ (σ (k y (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq982 y (M.op x y)
       grind)
    | (have r₁ := eq20207
       have r₂ := eq982 y (M.op x y)
       grind)
    | exact resolve eq20207 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq20207
  have eq20508 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75 eq20413
    | exact resolve eq20413 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq20413
  have eq20564 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20508
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20508
    | exact resolve eq20508 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20508
  have eq20611 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq20564
    | exact resolve eq20564 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20564
  have eq20635 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20611
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20611
    | exact resolve eq20611 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20611
  have eq22125 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17080 eq53
    | exact resolve eq53 eq17080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17080
  have eq23213 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq901 eq22125
    | exact resolve eq22125 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23345 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23213 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23213
  have eq78318 : (σ y) ≠ (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq20635
       have i₂ := eq94 sF3 sF1
       grind)
    | exact superpose eq94 eq20635
    | (have j1 := eq94 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq20635 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20635
  have eq78319 : (σ y) ≠ (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq78318
  have eq78324 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq78319
       have r₂ := eq23345 (σ y)
       grind)
    | exact resolve eq78319 eq23345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23345 eq78319
  have eq78339 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78324 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq78324
       grind)
    | exact resolve eq12 eq78324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78340 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78324 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ y)
       have r₂ := eq78324
       grind)
    | exact resolve eq13 eq78324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78324
  have eq78384 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq78340
  have eq78385 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq78339
  have eq78395 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq78385
       have r₂ := eq7796
       grind)
    | exact resolve eq78385 eq7796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7796 eq78385
  have eq78500 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78384 eq3449
    | exact resolve eq3449 eq78384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449 eq78384
  have eq78510 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq78500
  have eq78569 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78510 eq12299
    | exact resolve eq12299 eq78510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12299 eq78510
  have eq78588 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq78569
       have r₂ := eq22125 (σ (M.op x y))
       grind)
    | exact resolve eq78569 eq22125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22125 eq78569
  have eq78721 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78588 eq78395
    | exact resolve eq78395 eq78588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78395 eq78588
  have eq78773 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq78721
  have eq78787 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78773 eq13
    | exact resolve eq13 eq78773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78773
  have eq78838 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq78787
       have r₂ := eq901
       grind)
    | exact resolve eq78787 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq78787
  have eq79060 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78838 eq175
    | exact resolve eq175 eq78838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq78838
  have eq79091 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq79060
    | exact resolve eq79060 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq79060
  have eq79118 : y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79091 eq934
    | exact resolve eq934 eq79091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934 eq79091
  have eq79148 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq79118
  have eq79626 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94 y y
       have i₂ := eq79148
       grind)
    | exact superpose eq79148 eq94
    | (have j0 := eq94 y y
       grind)
    | exact resolve eq94 eq79148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq79148
  have eq79637 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq79626
  have eq81948 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1296 X0
       have i₂ := eq79637
       grind)
    | exact superpose eq79637 eq1296
    | exact resolve eq1296 eq79637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296 eq79637
  have eq81996 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq81948 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81948
  have eq81997 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq81996 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81996
    | (have j0 := eq81996 X0
       grind)
    | exact resolve eq81996 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81996
  have eq82715 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq776 eq81997
    | exact resolve eq81997 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq81997
  have eq83041 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq82715 X0
       grind)
    | (have r₁ := eq82715 X0
       have r₂ := eq893
       grind)
    | exact resolve eq82715 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq82715
  have eq83702 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq83041 x
       grind)
    | exact superpose eq83041 eq18
    | (have j1 := eq83041 x
       grind)
    | exact resolve eq18 eq83041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq83041
  have eq83720 : x = (M.op x y) := by grind
  clear eq83702
  have eq84032 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq83720 eq20
    | exact resolve eq20 eq83720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq84084 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 := by
    intro X0
    first
    | exact superpose eq83720 eq220
    | exact resolve eq220 eq83720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq83720
  have eq84196 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq84032
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq84032
    | exact resolve eq84032 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq84032
  have eq84202 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq84196 eq26
    | exact resolve eq26 eq84196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq84196
  have eq85850 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 y X0 x
       have i₂ := eq84084 y
       grind)
    | exact superpose eq84084 eq53
    | exact resolve eq53 eq84084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85853 : ∀ X0 : G, y ≠ X0 ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq521 X0 y x
       have i₂ := eq84084 y
       grind)
    | exact superpose eq84084 eq521
    | (have r₁ := eq521 y y x
       have r₂ := eq84084 y
       grind)
    | (have r₁ := eq521 (M.op (M.op x (M.op x (M.op x x))) (M.op x (M.op y x))) x x
       have r₂ := eq84084 (M.op x (M.op x (M.op x x)))
       grind)
    | exact resolve eq521 eq84084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq84084
  have eq94247 : (k y y) = (M.op y y) := by
    first
    | (have j0 := eq85853 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85853
  have eq94248 : y = (k y y) := by
    first
    | (have i₁ := eq94247
       have i₂ := eq85850 y
       grind)
    | exact superpose eq85850 eq94247
    | exact resolve eq94247 eq85850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85850 eq94247
  have eq94429 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq987 y y
       have i₂ := eq94248
       grind)
    | exact superpose eq94248 eq987
    | exact resolve eq987 eq94248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987 eq94248
  have eq94432 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq94429
  have eq94438 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq94432
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq94432
    | exact resolve eq94432 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq94432
  have eq94487 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq94438 eq53
    | exact resolve eq53 eq94438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq94569 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq94438 eq94487
    | exact resolve eq94487 eq94438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94487
  have eq94622 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq94438 eq94569
    | exact resolve eq94569 eq94438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94438 eq94569
  have eq95135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq94622 eq84202
    | exact resolve eq84202 eq94622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84202 eq94622
  have eq95165 : False := by grind
  exact eq95165

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq9 X0 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq527 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq500 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq544 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq527 (σ X1) (σ X0)
       grind)
    | exact superpose eq527 eq15
    | (have j1 := eq527 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq527 (τ X1) X0
       grind)
    | exact superpose eq527 eq18
    | (have j1 := eq527 (τ X1) X0
       grind)
    | exact resolve eq18 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq527
  have eq558 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq552
    | exact resolve eq552 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq558
    | (have j0 := eq558 X0 X1
       grind)
    | exact resolve eq558 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq802 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq544 x y
       grind)
    | exact superpose eq544 eq16
    | (have j1 := eq544 x y
       grind)
    | exact resolve eq16 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq544 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq826 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq814 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq814
    | (have j0 := eq814 (τ X1) (τ X0)
       grind)
    | exact resolve eq814 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq834 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq826 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq826
    | (have j0 := eq826 X0 X1
       grind)
    | exact resolve eq826 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq836 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq834 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq834
    | (have j0 := eq834 X0 X1
       grind)
    | exact resolve eq834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq837 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq836 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq836
    | (have j0 := eq836 X0 X1
       grind)
    | exact resolve eq836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq838 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq837 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq837
    | (have j0 := eq837 X0 X1
       grind)
    | exact resolve eq837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq926 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq802
       have i₂ := eq590 y x
       grind)
    | exact superpose eq590 eq802
    | (have j1 := eq590 (σ y) (σ x)
       grind)
    | (have r₁ := eq802
       have r₂ := eq590 y x
       grind)
    | exact resolve eq802 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq802
  have eq927 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq926
  have eq935 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq63 (σ x) X0 (σ y)
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq63
    | exact resolve eq63 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq974 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq63 (σ y) X0 (σ x)
       have i₂ := eq935 (σ y)
       grind)
    | exact superpose eq935 eq63
    | exact resolve eq63 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq1005 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  have eq1026 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1005
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq1005
    | exact resolve eq1005 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1206 : (σ y) = (σ (k y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq974 (σ y)
       have i₂ := eq1026
       grind)
    | exact superpose eq1026 eq974
    | exact resolve eq974 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq1026
  have eq1217 : (σ y) = (σ (k y y)) ∨ x = (M.op x y) := by grind
  clear eq1206
  have eq1229 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq1217
       grind)
    | exact superpose eq1217 eq10
    | exact resolve eq10 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1270 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1229
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1229
    | exact resolve eq1229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1278 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq838 y y
       have i₂ := eq1270
       grind)
    | exact superpose eq1270 eq838
    | (have j0 := eq838 y y
       grind)
    | (have r₁ := eq838 y y
       have r₂ := eq1270
       grind)
    | exact resolve eq838 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq1270
  have eq1281 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1278
  have eq1288 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq9
    | exact resolve eq9 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1429 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1288 X0
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1288
    | exact resolve eq1288 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1462 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1465 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1462 X0
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1462
    | exact resolve eq1462 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq1462
  have eq1498 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1465 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1533 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq1498 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1534 : x = (M.op x y) := by grind
  clear eq1533
  have eq1548 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 x X0 y
       have i₂ := eq1534
       grind)
    | exact superpose eq1534 eq63
    | exact resolve eq63 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1592 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 y X0 x
       have i₂ := eq1548 y
       grind)
    | exact superpose eq1548 eq63
    | exact resolve eq63 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1628 : (k y y) = (M.op y y) := by grind
  have eq1659 : y = (k y y) := by
    first
    | (have i₁ := eq1628
       have i₂ := eq1592 y
       grind)
    | exact superpose eq1592 eq1628
    | exact resolve eq1628 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1669 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq814 y y
       have i₂ := eq1659
       grind)
    | exact superpose eq1659 eq814
    | (have j0 := eq814 y y
       grind)
    | exact resolve eq814 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq1659
  have eq1674 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1669
  have eq1752 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 (σ y) X0 (σ y)
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq63
    | exact resolve eq63 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1759 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1752 X0
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq1752
    | exact resolve eq1752 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq1766 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1759 X0
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq1759
    | exact resolve eq1759 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674 eq1759
  have eq1792 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1766 (σ x)
       grind)
    | exact superpose eq1766 eq16
    | exact resolve eq16 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq1798 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1792
       have i₂ := eq1592 x
       grind)
    | exact superpose eq1592 eq1792
    | exact resolve eq1792 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592 eq1792
  have eq1799 : False := by grind
  exact eq1799

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_x_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq85 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq102 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq104 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq85 X1 X0
       grind)
    | (have r₁ := eq102 X1 X0
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq102 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq102 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq102
  have eq170 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq104
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq104 (σ X0) X1
       grind)
    | exact superpose eq104 eq15
    | (have j1 := eq104 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq184 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq170 X1 (τ X0)
       grind)
    | exact superpose eq170 eq18
    | (have j1 := eq170 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq170
  have eq483 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq184 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq184
    | exact resolve eq184 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq527 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq483 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq483
    | (have j0 := eq483 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq1735 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175 x y
       grind)
    | exact superpose eq175 eq16
    | (have j1 := eq175 x y
       grind)
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1757 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1735
       have i₂ := eq527 x y
       grind)
    | exact superpose eq527 eq1735
    | (have j1 := eq527 (σ x) (σ y)
       grind)
    | (have r₁ := eq1735
       have r₂ := eq527 x y
       grind)
    | (have r₁ := eq1735
       have r₂ := eq527 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1735
       have r₂ := eq527 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1735 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq1735
  have eq1758 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1757
  have eq1850 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1758
       grind)
    | exact superpose eq1758 eq16
    | exact resolve eq16 eq1758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq1851 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1850
       have r₂ := eq41 x
       grind)
    | exact resolve eq1850 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq1852 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1851
       grind)
    | exact superpose eq1851 eq16
    | exact resolve eq16 eq1851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1853 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1851
       grind)
    | exact superpose eq1851 eq10
    | exact resolve eq10 eq1851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851
  have eq1897 : x = y := by
    first
    | (have i₁ := eq1853
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1853
    | exact resolve eq1853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq1898 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1852
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq1852
    | exact resolve eq1852 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1852
  have eq1899 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1898
       have i₂ := eq1897
       grind)
    | exact superpose eq1897 eq1898
    | exact resolve eq1898 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897 eq1898
  have eq1900 : False := by grind
  exact eq1900

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq38 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq43
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq50 X0 X1
       grind)
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq100 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq53 X0 X1
       grind)
    | (have r₁ := eq96 X0 X1
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq96 X0 X0
       have r₂ := eq53 X0 X0
       grind)
    | exact resolve eq96 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq96
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X0) (σ X1)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq211
    | exact resolve eq211 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq211
  have eq220 : False := by grind
  exact eq220

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
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
  clear eq17
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq22
  have eq264 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq265 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq264
    | (have j0 := eq264 (σ X0) (σ X1)
       grind)
    | exact resolve eq264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq264
    | (have j0 := eq264 (τ X0) (τ X1)
       grind)
    | exact resolve eq264 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq293 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 X1
       have i₂ := eq264 X0 X1
       grind)
    | exact superpose eq264 eq265
    | (have j0 := eq265 X0 X1
       have j1 := eq264 (σ X0) (σ X1)
       grind)
    | exact resolve eq265 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq537 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq266 X0 X0
       grind)
    | exact superpose eq266 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq266 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X1)
       have r₂ := eq266 X1 X1
       grind)
    | exact resolve eq12 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq542 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq537 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq537 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq537 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq549 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq540 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq540
    | (have j0 := eq540 (σ X0) (σ X1)
       grind)
    | exact resolve eq540 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq559 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq549 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq549
    | (have j0 := eq549 X0 X1
       grind)
    | exact resolve eq549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq561 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq559
    | (have j0 := eq559 X0 X1
       grind)
    | exact resolve eq559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq562 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq561 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq561
    | (have j0 := eq561 X0 X1
       grind)
    | exact resolve eq561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq563 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq562
    | (have j0 := eq562 X0 X1
       grind)
    | exact resolve eq562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq565 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq563 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq563
    | (have j0 := eq563 (σ X0) (σ X1)
       grind)
    | exact resolve eq563 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq620 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq542 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq542
    | (have j0 := eq542 (σ X0) X1
       grind)
    | exact resolve eq542 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq621 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | exact resolve eq620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq624 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq621 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq621
    | (have j0 := eq621 X0 X1
       grind)
    | exact resolve eq621 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq629 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq624 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq624
    | (have j0 := eq624 (σ X0) X1
       grind)
    | exact resolve eq624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq5003 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq293 x y
       grind)
    | exact superpose eq293 eq16
    | (have j1 := eq293 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq293 x y
       grind)
    | exact resolve eq16 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq5018 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5003
  have eq5039 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5018
       grind)
    | exact superpose eq5018 eq16
    | exact resolve eq16 eq5018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5040 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq5018
       grind)
    | exact superpose eq5018 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq5018
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq5018
       grind)
    | exact resolve eq13 eq5018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5018
  have eq5041 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5040
  have eq5043 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5041
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5041
    | exact resolve eq5041 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5041
  have eq5045 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq264 eq5043
    | (have j1 := eq264 (σ y) (σ y)
       grind)
    | exact resolve eq5043 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq5043
  have eq5046 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5045
       have r₂ := eq5039
       grind)
    | exact resolve eq5045 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039 eq5045
  have eq5049 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq5046
       grind)
    | exact superpose eq5046 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq5046
       grind)
    | exact resolve eq12 eq5046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5053 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5049 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5049
  have eq5055 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5053 (σ X0)
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq5053
    | exact resolve eq5053 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5085 : ∀ X0 : G, (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq542 (σ y) X0
       have i₂ := eq5053 (σ y)
       grind)
    | exact superpose eq5053 eq542
    | (have j0 := eq542 (σ y) X0
       grind)
    | exact resolve eq542 eq5053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq5053
  have eq5168 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ y))) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5085 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5085
    | (have j0 := eq5085 X0
       grind)
    | exact resolve eq5085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5085
  have eq5183 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5168 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5168
    | exact resolve eq5168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5168
  have eq5186 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y ≠ (τ (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5046 eq5183
    | (have j0 := eq5183 X0
       grind)
    | exact resolve eq5183 eq5046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5046 eq5183
  have eq5189 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5186 X0
       grind)
    | (have r₁ := eq5186 X0
       have r₂ := eq10 y
       grind)
    | exact resolve eq5186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186
  have eq5395 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5189 eq5055
    | exact resolve eq5055 eq5189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5055 eq5189
  have eq5412 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5395 x
       grind)
    | exact superpose eq5395 eq16
    | (have r₁ := eq16
       have r₂ := eq5395 x
       grind)
    | exact resolve eq16 eq5395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5395
  have eq5432 : y = (M.op x y) := by grind
  clear eq5412
  have eq5465 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5432
       grind)
    | exact superpose eq5432 eq16
    | exact resolve eq16 eq5432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5466 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq5432
       grind)
    | exact superpose eq5432 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq5432
       grind)
    | exact resolve eq13 eq5432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5467 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq5466
  have eq5475 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq565 x y
       have i₂ := eq5467
       grind)
    | exact superpose eq5467 eq565
    | (have j0 := eq565 x y
       grind)
    | exact resolve eq565 eq5467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq5467
  have eq5478 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq5475
  have eq5485 : y = (M.op y y) := by
    first
    | (have r₁ := eq5478
       have r₂ := eq5465
       grind)
    | exact resolve eq5478 eq5465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5478
  have eq5599 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq5485
       grind)
    | exact superpose eq5485 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq5485
       grind)
    | exact resolve eq12 eq5485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5603 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq5599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5599
  have eq5607 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq629 y X0
       have i₂ := eq5603 y
       grind)
    | exact superpose eq5603 eq629
    | (have j0 := eq629 y X0
       grind)
    | exact resolve eq629 eq5603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq5651 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5607 X0
       have i₂ := eq5485
       grind)
    | exact superpose eq5485 eq5607
    | (have j0 := eq5607 X0
       grind)
    | exact resolve eq5607 eq5485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5485 eq5607
  have eq5652 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq5651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5651
  have eq5835 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq5652 (σ X0)
       grind)
    | exact superpose eq5652 eq15
    | exact resolve eq15 eq5652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5652
  have eq5923 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq5835 X0
       have i₂ := eq5603 X0
       grind)
    | exact superpose eq5603 eq5835
    | exact resolve eq5835 eq5603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5603 eq5835
  have eq6400 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq5465
       have i₂ := eq5923 x
       grind)
    | exact superpose eq5923 eq5465
    | exact resolve eq5465 eq5923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465 eq5923
  have eq6443 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6400
       have i₂ := eq5432
       grind)
    | exact superpose eq5432 eq6400
    | exact resolve eq6400 eq5432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5432 eq6400
  have eq6444 : False := by grind
  exact eq6444

/-- `Equation115`: `x = y ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation115 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law115 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law115.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq9 X0 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq65 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq10
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq578 : ∀ X0 X1 : G, (M.op X0 (τ X1)) ≠ (M.op (τ X1) X0) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq13 X0 (τ X1)
       grind)
    | exact superpose eq13 eq20
    | (have j1 := eq13 X0 (τ X1)
       grind)
    | exact resolve eq20 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) ≠ (M.op (k X1 (σ X2)) (σ X0)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X1 X2 X0
       have i₂ := eq13 (σ X0) (k X1 (σ X2))
       grind)
    | exact superpose eq13 eq27
    | (have j1 := eq13 (σ X0) (k X1 (σ X2))
       grind)
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X0 X1 X2
       have i₂ := eq14 (σ X2) (k X0 (σ X1))
       grind)
    | exact superpose eq14 eq27
    | (have j1 := eq14 (k X0 (σ X1)) (σ X2)
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq6065 : ∀ X0 X1 : G, (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (M.op (M.op (M.op X0 X0) (τ X1)) (τ X1)) = X0 ∨ (σ X0) = (k (σ (M.op (M.op X0 X0) (τ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq788 X0 (M.op (M.op X0 X0) (τ X0))
       have i₂ := eq9 X0 (τ X0)
       grind)
    | exact superpose eq9 eq788
    | (have j0 := eq788 X1 (M.op (M.op X0 X0) (τ X1))
       grind)
    | exact resolve eq788 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq446629 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 ∨ (M.op (M.op (M.op X1 X1) X0) X0) = X1 ∨ (σ X1) = (k (σ (M.op (M.op X1 X1) X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6065 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6065
    | exact resolve eq6065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6065
  have eq446983 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) X0) = X1 ∨ (M.op (M.op X1 X1) X0) = X0 ∨ (σ X1) = (σ (k (M.op (M.op X1 X1) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq446629 X0 X1
       have i₂ := eq15 (M.op (M.op X1 X1) X0) X0
       grind)
    | exact superpose eq15 eq446629
    | (have j0 := eq446629 X0 X1
       grind)
    | exact resolve eq446629 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446629
  have eq447315 : ∀ X0 X1 : G, (M.op (τ X1) (M.op (M.op X0 X0) (τ X1))) ≠ X0 ∨ (σ X0) = (k (σ (M.op (M.op X0 X0) (τ X1))) X1) ∨ (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq578 (M.op (M.op X1 X1) (τ X1)) X1
       have i₂ := eq446983 (τ X1) X1
       grind)
    | exact superpose eq446983 eq578
    | (have j0 := eq578 (M.op (M.op X0 X0) (τ X1)) X1
       have j1 := eq446983 (τ X1) X0
       grind)
    | exact resolve eq578 eq446983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq446983
  have eq447346 : ∀ X0 X1 : G, (M.op (τ X1) (M.op (M.op X0 X0) (τ X1))) ≠ X0 ∨ (σ X0) = (k (σ (M.op (M.op X0 X0) (τ X1))) X1) ∨ (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq447315 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447315
  have eq447569 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op (M.op X0 X0) (τ X1))) X1) ∨ (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq447346 X0 X1
       grind)
    | (have r₁ := eq447346 X0 X1
       have r₂ := eq9 X0 (τ X1)
       grind)
    | exact resolve eq447346 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447346
  have eq447802 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op (M.op X0 X0) (τ X1))) X1) ∨ (σ X0) = (k (σ (M.op (M.op X0 X0) (τ X1))) X1) ∨ (τ X1) = (M.op (M.op X0 X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq447569 X0 X1
       have i₂ := eq20 X1 (M.op (M.op X0 X0) (τ X1))
       grind)
    | exact superpose eq20 eq447569
    | (have j0 := eq447569 X0 X1
       grind)
    | exact resolve eq447569 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq447569
  have eq447803 : ∀ X0 X1 : G, (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (σ X0) = (k (σ (M.op (M.op X0 X0) (τ X1))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq447802 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447802
  have eq448369 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = X1 ∨ (σ X1) = (k (σ (M.op (M.op X1 X1) (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq447803 X1 X0
       grind)
    | exact superpose eq447803 eq9
    | (have j1 := eq447803 X1 X0
       grind)
    | exact resolve eq9 eq447803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447803
  have eq448623 : ∀ X0 X1 : G, (σ X1) = (k (σ (M.op (M.op X1 X1) (τ X0))) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq448369 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq448369
    | (have j0 := eq448369 X0 X1
       grind)
    | exact resolve eq448369 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448369
  have eq448669 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ (M.op X0 X0)) (τ X1))) X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq448623 X1 (τ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq448623
    | (have j0 := eq448623 X1 (τ X0)
       grind)
    | exact resolve eq448623 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq449190 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X0 X0) (τ (σ X1))))) X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ (M.op (M.op X0 X0) (τ (σ X1)))) X1
       have i₂ := eq448623 (σ X1) X0
       grind)
    | exact superpose eq448623 eq29
    | (have j1 := eq448623 (σ X1) X0
       grind)
    | exact resolve eq29 eq448623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq448623
  have eq449647 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) (τ (σ X1))) X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq449190 X0 X1
       have i₂ := eq10 (M.op (M.op X0 X0) (τ (σ X1)))
       grind)
    | exact superpose eq10 eq449190
    | (have j0 := eq449190 X0 X1
       grind)
    | exact resolve eq449190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449190
  have eq449919 : ∀ X0 X1 : G, (k (σ (M.op (τ (M.op X0 X0)) (τ X1))) X1) = X0 ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq448669 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq448669
    | (have j0 := eq448669 X0 X1
       grind)
    | exact resolve eq448669 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448669
  have eq450064 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) X1) X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq449647 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq449647
    | (have j0 := eq449647 X0 X1
       grind)
    | exact resolve eq449647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449647
  have eq450272 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X1) X1) = X0 ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq450064 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq450064
    | (have j0 := eq450064 X0 X1
       grind)
    | exact resolve eq450064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450064
  have eq450404 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (k (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq450272 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq450272
    | (have j0 := eq450272 X0 X1
       grind)
    | exact resolve eq450272 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450272
  have eq450481 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X1) X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq450404 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq450404
    | (have j0 := eq450404 X0 X1
       grind)
    | exact resolve eq450404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450404
  have eq1343918 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ X2) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq587 X2 X0 X1
       have i₂ := eq797 X0 X1 X2
       grind)
    | exact superpose eq797 eq587
    | (have j0 := eq587 X2 X0 X1
       have j1 := eq797 X0 X1 X2
       grind)
    | (have r₁ := eq587 X2 X0 X1
       have r₂ := eq797 X0 X1 X2
       grind)
    | exact resolve eq587 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq797
  have eq1344529 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1343918 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343918
  have eq1344530 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1344529 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344529
  have eq1346365 : ∀ X0 X1 X2 : G, (k X2 (σ (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ (τ X2))) ∨ (k X0 (σ X1)) = (σ (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (k (τ X0) X1)
       have i₂ := eq1344530 X0 X1 (τ X2)
       grind)
    | exact superpose eq1344530 eq19
    | (have j1 := eq1344530 X0 X1 (τ X2)
       grind)
    | exact resolve eq19 eq1344530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344530
  have eq1346855 : ∀ X0 X1 X2 : G, (k X2 (σ (k (τ X0) X1))) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (σ (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1346365 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq1346365
    | (have j0 := eq1346365 X0 X1 X2
       grind)
    | exact resolve eq1346365 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346365
  have eq1347152 : ∀ X0 X1 X2 : G, (k X2 (k X0 (σ X1))) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (σ (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1346855 X0 X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1346855
    | (have j0 := eq1346855 X0 X1 X2
       grind)
    | exact resolve eq1346855 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346855
  have eq1347415 : ∀ X0 X1 X2 : G, (k X2 (k X0 (σ X1))) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1347152 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq1347152
    | (have j0 := eq1347152 X0 X1 X2
       grind)
    | exact resolve eq1347152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347152
  have eq1347950 : ∀ X0 X1 X2 : G, (k X1 (k X2 X0)) = (M.op (k X2 X0) X1) ∨ (k X2 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1347415 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1347415
    | exact resolve eq1347415 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1348190 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (τ X0) = (τ (M.op (σ X2) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1347415 (σ (M.op (τ (M.op X0 X0)) (τ (σ X1)))) X1 X2
       have i₂ := eq449919 X0 (σ X1)
       grind)
    | exact superpose eq449919 eq1347415
    | (have j1 := eq449919 X0 (σ X2)
       grind)
    | exact resolve eq1347415 eq449919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449919 eq1347415
  have eq1350099 : ∀ X0 X1 X2 : G, (τ X0) = (τ (σ (M.op X2 X2))) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1348190 X0 X1 X2
       have i₂ := eq23 X2
       grind)
    | exact superpose eq23 eq1348190
    | (have j0 := eq1348190 X0 X1 X2
       grind)
    | exact resolve eq1348190 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348190
  have eq1350191 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ X0) = (M.op X2 X2) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1350099 X0 X1 X2
       have i₂ := eq10 (M.op X2 X2)
       grind)
    | exact superpose eq10 eq1350099
    | (have j0 := eq1350099 X0 X1 X2
       grind)
    | exact resolve eq1350099 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350099
  have eq1350435 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1347950 X1 X1 (M.op (M.op X0 X0) X1)
       have i₂ := eq450481 X0 X1
       grind)
    | exact superpose eq450481 eq1347950
    | (have j0 := eq1347950 X0 (M.op X0 X1) X1
       have j1 := eq450481 X0 X2
       grind)
    | exact resolve eq1347950 eq450481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450481 eq1347950
  have eq1353923 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1350435 X0 (τ X1) X2
       grind)
    | exact superpose eq1350435 eq19
    | (have j1 := eq1350435 (k X1 (σ X0)) (σ (M.op X0 (τ X1))) X2
       grind)
    | exact resolve eq19 eq1350435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1350435
  have eq1357535 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X2 X2) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1350191 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq1350191 eq15
    | (have j1 := eq1350191 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq15 eq1350191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350191
  have eq1358430 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1357535 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1357535
    | (have j0 := eq1357535 X0 X1 X2
       grind)
    | exact resolve eq1357535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357535
  have eq1465841 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1353923 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1353923
    | (have j0 := eq1353923 X1 X1 X2
       grind)
    | exact resolve eq1353923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353923
  have eq1466789 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1465841 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1465841
    | (have j0 := eq1465841 X0 X1 X2
       grind)
    | exact resolve eq1465841 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465841
  have eq1581732 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1358430 x y X0
       grind)
    | exact superpose eq1358430 eq16
    | (have j1 := eq1358430 x y X0
       grind)
    | exact resolve eq16 eq1358430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358430
  have eq1583148 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1581732 X0
       have i₂ := eq1466789 y x X1
       grind)
    | exact superpose eq1466789 eq1581732
    | (have j0 := eq1581732 X0
       have j1 := eq1466789 (M.op X0 X0) x X0
       grind)
    | (have r₁ := eq1581732 X0
       have r₂ := eq1466789 y x x
       grind)
    | (have r₁ := eq1581732 X0
       have r₂ := eq1466789 (σ (M.op x y)) (σ (k y x)) x
       grind)
    | (have r₁ := eq1581732 X0
       have r₂ := eq1466789 (σ (k y x)) (σ (M.op x y)) x
       grind)
    | exact resolve eq1581732 eq1466789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466789 eq1581732
  have eq1583171 : ∀ X0 X1 : G, x = y ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = x ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1583148 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583148
  have eq1583196 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = x ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1583171 X0 X1
       grind)
    | exact superpose eq1583171 eq16
    | (have j1 := eq1583171 X0 X0
       grind)
    | exact resolve eq16 eq1583171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583171
  have eq1583198 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (M.op X0 X0) = x ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1583196 X0 X0
       grind)
    | (have r₁ := eq1583196 X0 X1
       have r₂ := eq23 x
       grind)
    | exact resolve eq1583196 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583196
  have eq1583200 : ∀ X0 X1 : G, y = (τ (σ x)) ∨ (M.op X0 X0) = x ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 y
       have i₂ := eq1583198 X0 X1
       grind)
    | exact superpose eq1583198 eq10
    | (have j1 := eq1583198 X0 X0
       grind)
    | exact resolve eq10 eq1583198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583198
  have eq1583704 : ∀ X0 X1 : G, x = y ∨ (M.op X0 X0) = x ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1583200 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1583200
    | (have j0 := eq1583200 X0 X0
       grind)
    | exact resolve eq1583200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583200
  have eq1583706 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = x ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1583704 X0 X1
       grind)
    | exact superpose eq1583704 eq16
    | (have j1 := eq1583704 X0 X0
       grind)
    | exact resolve eq16 eq1583704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583704
  have eq1583708 : ∀ X0 X1 : G, (M.op X0 X0) = x ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1583706 X0 X0
       grind)
    | (have r₁ := eq1583706 X0 X1
       have r₂ := eq23 x
       grind)
    | exact resolve eq1583706 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1583706
  have eq1585395 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq1583708 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583708
  have eq1585396 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq1585395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585395
  have eq1585421 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq1585396 X1
       grind)
    | exact superpose eq1585396 eq9
    | exact resolve eq9 eq1585396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1586558 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18 X0 X0
       have i₂ := eq1585396 (M.op X0 X0)
       grind)
    | exact superpose eq1585396 eq18
    | exact resolve eq18 eq1585396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1586689 : ∀ X0 : G, (M.op (M.op X0 X0) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq1585396 (M.op X0 X0)
       grind)
    | exact superpose eq1585396 eq9
    | exact resolve eq9 eq1585396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1587422 : ∀ X0 : G, (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1586689 X0
       have i₂ := eq1585396 X0
       grind)
    | exact superpose eq1585396 eq1586689
    | exact resolve eq1586689 eq1585396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586689
  have eq1588536 : ∀ X0 X1 : G, (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1585421 X0 X1
       have i₂ := eq1586558 X0
       grind)
    | exact superpose eq1586558 eq1585421
    | exact resolve eq1585421 eq1586558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585421 eq1586558
  have eq1588831 : ∀ X0 : G, x = X0 := by
    intro X0
    first
    | (have i₁ := eq1587422 X0
       have i₂ := eq1585396 x
       grind)
    | exact superpose eq1585396 eq1587422
    | exact resolve eq1587422 eq1585396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585396 eq1587422
  have eq1599799 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1588831 y
       grind)
    | exact superpose eq1588831 eq16
    | exact resolve eq16 eq1588831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588831
  have eq1599801 : False := by grind
  exact eq1599801

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation1242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq4138 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq86 X1 X0
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq86 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq86 X0 (σ X0)
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4147 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq4148 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147
  have eq4149 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4138 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4138
  have eq4150 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149
  have eq4152 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4148 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4148
    | (have j0 := eq4148 X0
       grind)
    | exact resolve eq4148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148
  have eq4197 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq4152 X0
       grind)
    | exact superpose eq4152 eq38
    | (have j1 := eq4152 X0
       grind)
    | exact resolve eq38 eq4152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq4152
  have eq4213 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4197 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4197
    | (have j0 := eq4197 X0
       grind)
    | exact resolve eq4197 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4197
  have eq4214 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4213 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213
  have eq4216 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4214 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4214
    | exact resolve eq4214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4238 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4214 X0
       grind)
    | exact superpose eq4214 eq11
    | exact resolve eq11 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214
  have eq4297 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4216 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq4216
    | exact resolve eq4216 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4216
  have eq4516 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4297 X0
       grind)
    | exact superpose eq4297 eq11
    | exact resolve eq11 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4625 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4516 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4516
    | exact resolve eq4516 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4516
  have eq4687 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq4625 (τ X0)
       grind)
    | exact superpose eq4625 eq34
    | exact resolve eq34 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4741 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4687 X0
       have i₂ := eq4297 X0
       grind)
    | exact superpose eq4297 eq4687
    | exact resolve eq4687 eq4297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4297 eq4687
  have eq5278 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5295 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5278 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5278
    | exact resolve eq5278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5278
  have eq5329 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5295 X0
       have i₂ := eq4625 X0
       grind)
    | exact superpose eq4625 eq5295
    | exact resolve eq5295 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5295
  have eq5344 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5329
  have eq23529 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) X0
       have i₂ := eq4150 (σ X0) X1
       grind)
    | exact superpose eq4150 eq24
    | (have j1 := eq4150 (σ X0) X1
       grind)
    | exact resolve eq24 eq4150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4150
  have eq23612 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23529 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq23529
    | (have j0 := eq23529 X0 X1
       grind)
    | exact resolve eq23529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23529
  have eq23688 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23612 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23612
    | (have j0 := eq23612 X0 X1
       grind)
    | exact resolve eq23612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23612
  have eq23756 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23688 X0 X1
       have i₂ := eq4238 X0
       grind)
    | exact superpose eq4238 eq23688
    | (have j0 := eq23688 X0 X1
       grind)
    | exact resolve eq23688 eq4238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23688
  have eq23802 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23756 X0 X1
       have i₂ := eq4625 X0
       grind)
    | exact superpose eq4625 eq23756
    | (have j0 := eq23756 X0 X1
       grind)
    | exact resolve eq23756 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23756
  have eq23840 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23802 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23802
    | (have j0 := eq23802 X0 X1
       grind)
    | exact resolve eq23802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23802
  have eq26921 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23840 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23840
    | (have j0 := eq23840 X1 (τ X0)
       grind)
    | exact resolve eq23840 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26998 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq23840 X1 X0
       grind)
    | exact superpose eq23840 eq11
    | (have j1 := eq23840 X1 X0
       grind)
    | exact resolve eq11 eq23840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23840
  have eq27411 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26921 X1 (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq26921
    | (have j0 := eq26921 X0 (τ X1)
       grind)
    | exact resolve eq26921 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq26921
  have eq27600 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27411 X0 X1
       have i₂ := eq4741 X1
       grind)
    | exact superpose eq4741 eq27411
    | (have j0 := eq27411 X0 X1
       grind)
    | exact resolve eq27411 eq4741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741 eq27411
  have eq27683 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27600 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq27600
    | (have j0 := eq27600 X0 X1
       grind)
    | exact resolve eq27600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27600
  have eq27758 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27683 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27683
    | (have j0 := eq27683 X0 X1
       grind)
    | exact resolve eq27683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27683
  have eq28646 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27758 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27758
  have eq30957 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26998 x y
       grind)
    | exact superpose eq26998 eq16
    | (have j1 := eq26998 x y
       grind)
    | exact resolve eq16 eq26998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26998
  have eq31421 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30957
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq30957
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq30957 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30957
  have eq31424 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq31421
  have eq31425 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq31424
  have eq31624 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28646 x y
       have i₂ := eq31425
       grind)
    | exact superpose eq31425 eq28646
    | (have j0 := eq28646 x y
       grind)
    | exact resolve eq28646 eq31425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28646
  have eq31625 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq31624
  have eq31626 : x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq31625
  have eq31866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5344 y
       have i₂ := eq31626
       grind)
    | exact superpose eq31626 eq5344
    | exact resolve eq5344 eq31626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31626
  have eq31889 : (σ x) = (σ (M.op y y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq31866
       have r₂ := eq16
       grind)
    | exact resolve eq31866 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31866
  have eq31907 : (M.op y y) = (τ (σ x)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq31889
       grind)
    | exact superpose eq31889 eq10
    | exact resolve eq10 eq31889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31889
  have eq32039 : x = (M.op y y) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq31907
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31907
    | exact resolve eq31907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31907
  have eq32667 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq5344 y
       have i₂ := eq32039
       grind)
    | exact superpose eq32039 eq5344
    | exact resolve eq5344 eq32039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32039
  have eq32690 : (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq32667
       have r₂ := eq16
       grind)
    | exact resolve eq32667 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32667
  have eq32706 : (k x y) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq32690
       grind)
    | exact superpose eq32690 eq11
    | exact resolve eq11 eq32690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32690
  have eq32874 : y = (k x y) := by
    first
    | (have i₁ := eq32706
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq32706
    | exact resolve eq32706 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32706
  have eq33353 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq210 x y
       have i₂ := eq32874
       grind)
    | exact superpose eq32874 eq210
    | (have j0 := eq210 x y
       grind)
    | exact resolve eq210 eq32874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq32874
  have eq33362 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq33353
  have eq33367 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33362
       have i₂ := eq4238 y
       grind)
    | exact superpose eq4238 eq33362
    | exact resolve eq33362 eq4238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238 eq33362
  have eq33373 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq33367
       have i₂ := eq4625 y
       grind)
    | exact superpose eq4625 eq33367
    | exact resolve eq33367 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4625 eq33367
  have eq36345 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33373
       grind)
    | exact superpose eq33373 eq16
    | exact resolve eq16 eq33373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33373
  have eq36829 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq36345
       have i₂ := eq31425
       grind)
    | exact superpose eq31425 eq36345
    | exact resolve eq36345 eq31425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31425 eq36345
  have eq36830 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq36829
  have eq36831 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq36830
  have eq36848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5344 y
       have i₂ := eq36831
       grind)
    | exact superpose eq36831 eq5344
    | exact resolve eq5344 eq36831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36831
  have eq36871 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq36848
       have r₂ := eq16
       grind)
    | exact resolve eq36848 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36848
  have eq37306 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq36871
       grind)
    | exact superpose eq36871 eq10
    | exact resolve eq10 eq36871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36871
  have eq37440 : x = (M.op y y) := by
    first
    | (have i₁ := eq37306
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37306
    | exact resolve eq37306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37306
  have eq37547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5344 y
       have i₂ := eq37440
       grind)
    | exact superpose eq37440 eq5344
    | exact resolve eq5344 eq37440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5344 eq37440
  have eq37571 : False := by grind
  exact eq37571
