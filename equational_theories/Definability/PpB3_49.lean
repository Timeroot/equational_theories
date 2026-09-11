import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
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
  clear eq44
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq37
  have eq77 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq81 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq77 sF2
       grind)
    | exact superpose eq77 eq50
    | exact resolve eq50 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq82 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq81
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq81
    | exact resolve eq81 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq91 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq77 sF3
       grind)
    | exact superpose eq77 eq75
    | exact resolve eq75 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq92 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq91
    | exact resolve eq91 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq117 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq136 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq133
       have i₂ := eq77 sF1
       grind)
    | exact superpose eq77 eq133
    | exact resolve eq133 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq138 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq77 sF0
       grind)
    | exact superpose eq77 eq136
    | exact resolve eq136 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq136
  have eq159 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq253 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq290 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq159
       have i₂ := eq253 sF1 x
       grind)
    | (have i₁ := eq159
       have i₂ := eq253 X0 sF1
       grind)
    | exact superpose eq253 eq159
    | exact resolve eq159 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq400 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (τ (M.op x (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq290
    | exact resolve eq290 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq24305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq24306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq24305
    | exact resolve eq24305 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24305
  have eq24317 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq24306
       have r₂ := eq28
       grind)
    | exact resolve eq24306 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24306
  have eq24327 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq24317 eq117
    | exact resolve eq117 eq24317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq24317
  have eq24403 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq24327
    | exact resolve eq24327 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24327
  have eq24404 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24403
  have eq24409 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24404
       have i₂ := eq253 y X0
       grind)
    | (have i₁ := eq24404
       have i₂ := eq253 X0 y
       grind)
    | exact superpose eq253 eq24404
    | exact resolve eq24404 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq24404
  have eq24645 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq24409 (M.op x x)
       grind)
    | exact superpose eq24409 eq14
    | exact resolve eq14 eq24409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24690 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52 sF0
       have i₂ := eq24409 sF0
       grind)
    | exact superpose eq24409 eq52
    | exact resolve eq52 eq24409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq24695 : y = (τ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq400 sF0
       have i₂ := eq24409 sF0
       grind)
    | exact superpose eq24409 eq400
    | exact resolve eq400 eq24409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq24409
  have eq24799 : y = (τ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24695
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24695
    | exact resolve eq24695 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24695
  have eq24804 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24690
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24690
    | exact resolve eq24690 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24690
  have eq25019 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24804 eq30
    | exact resolve eq30 eq24804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24804
  have eq25111 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq25019
    | exact resolve eq25019 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25019
  have eq25112 : y = (M.op x y) ∨ x = y := by grind
  clear eq25111
  have eq25143 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq25112 eq21
    | exact resolve eq21 eq25112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25266 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25143
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25143
    | exact resolve eq25143 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25143
  have eq25609 : (σ y) = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24799 eq15
    | exact resolve eq15 eq24799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24799
  have eq25639 : (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25609
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25609
    | exact resolve eq25609 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25609
  have eq25642 : y = (τ (σ x)) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq25639 eq30
    | exact resolve eq30 eq25639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25639
  have eq25740 : x = y ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq25642
    | exact resolve eq25642 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25642
  have eq25741 : (M.op x y) = (σ y) ∨ x = y := by grind
  clear eq25740
  have eq25777 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq25741 eq27
    | exact resolve eq27 eq25741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25778 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq25741 eq30
    | exact resolve eq30 eq25741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25741
  have eq26071 : y = (τ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq25112 eq25778
    | exact resolve eq25778 eq25112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25778
  have eq26097 : y = (τ y) ∨ x = y := by grind
  clear eq26071
  have eq26143 : y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq26097
       grind)
    | exact superpose eq26097 eq15
    | exact resolve eq15 eq26097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26097
  have eq26172 : y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26143
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26143
    | exact resolve eq26143 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26143
  have eq26374 : y = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq26172 eq25266
    | exact resolve eq25266 eq26172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25266 eq26172
  have eq26379 : y = (σ (M.op x y)) ∨ x = y := by grind
  clear eq26374
  have eq26645 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq25112 eq25777
    | exact resolve eq25777 eq25112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25112 eq25777
  have eq26678 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = y := by grind
  clear eq26645
  have eq29021 : y = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26678
       have i₂ := eq24645 sF2
       grind)
    | exact superpose eq24645 eq26678
    | exact resolve eq26678 eq24645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24645 eq26678
  have eq29022 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq29021
  have eq29060 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29022 eq30
    | exact resolve eq30 eq29022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29022
  have eq29198 : x = y ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq29060
    | exact resolve eq29060 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29060
  have eq29199 : y = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq29198
  have eq29230 : y ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq29199 eq28
    | exact resolve eq28 eq29199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29199
  have eq29243 : x = y := by
    first
    | (have r₁ := eq29230
       have r₂ := eq26379
       grind)
    | exact resolve eq29230 eq26379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26379 eq29230
  have eq29244 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq29243
       grind)
    | exact superpose eq29243 eq19
    | exact resolve eq19 eq29243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29245 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq29243
       grind)
    | exact superpose eq29243 eq25
    | exact resolve eq25 eq29243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29243
  have eq29338 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29245
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29245
    | exact resolve eq29245 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29245
  have eq29372 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29338 eq27
    | exact resolve eq27 eq29338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29338
  have eq29656 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29372 eq82
    | exact resolve eq82 eq29372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq29372
  have eq29745 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq29656
       have i₂ := eq29244
       grind)
    | exact superpose eq29244 eq29656
    | exact resolve eq29656 eq29244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29244 eq29656
  have eq29764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29745 eq15
    | exact resolve eq15 eq29745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29745
  have eq29799 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq29764
    | exact resolve eq29764 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq29764
  have eq29806 : False := by grind
  exact eq29806

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) (k X0 X1)
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (k X0 X1) (M.op X1 X1)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq177 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op X1 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq181
    | exact resolve eq181 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq192 : ∀ X0 : G, (k X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq183 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq183
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq183 x X0
       have i₂ := eq183 x X1
       grind)
    | exact superpose eq183 eq183
    | exact resolve eq183 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq264 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1
       have i₂ := eq221 X1 X0
       grind)
    | (have i₁ := eq175 X1
       have i₂ := eq221 X0 X1
       grind)
    | exact superpose eq221 eq175
    | exact resolve eq175 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 x) X1 x
       have i₂ := eq221 (M.op X1 x) X1
       grind)
    | (have i₁ := eq16 (M.op X1 x) X1 x
       have i₂ := eq221 X0 (M.op X1 x)
       grind)
    | exact superpose eq221 eq16
    | exact resolve eq16 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq274 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq269 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq269
    | exact resolve eq269 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq303 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1
       have i₂ := eq264 X1 X0
       grind)
    | exact superpose eq264 eq175
    | exact resolve eq175 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (k X0 X0) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X1
       have i₂ := eq264 X1 X0
       grind)
    | exact superpose eq264 eq177
    | exact resolve eq177 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq314 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq264 X0 (σ X1)
       grind)
    | exact superpose eq264 eq10
    | exact resolve eq10 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq341 : ∀ X0 X1 : G, (k X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq303 (σ X1) X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq303 X0 (σ X1)
       grind)
    | exact superpose eq303 eq10
    | exact resolve eq10 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (k y y) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq116
       have i₂ := eq303 sF3 x
       grind)
    | (have i₁ := eq116
       have i₂ := eq303 X0 sF3
       grind)
    | exact superpose eq303 eq116
    | exact resolve eq116 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq403 : ∀ X0 X1 : G, (k (k X1 X1) y) = (τ (k (M.op X0 X0) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (k X1 X1)
       have i₂ := eq314 X0 X1
       grind)
    | exact superpose eq314 eq73
    | exact resolve eq73 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq314
  have eq406 : ∀ X0 X1 : G, (k (k X1 X1) y) = (k (τ (M.op X0 X0)) y) := by
    intro X0 X1
    first
    | exact superpose eq153 eq403
    | exact resolve eq403 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq403
  have eq437 : ∀ X0 X1 : G, (k (k X1 X1) y) = (k (τ (k X0 X0)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq406
    | exact resolve eq406 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq443 : ∀ X1 : G, (k (k X1 X1) y) = (k (k y y) y) := by
    intro X1
    first
    | (have i₁ := eq437 x X1
       have i₂ := eq347 x
       grind)
    | exact superpose eq347 eq437
    | exact resolve eq437 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq1144 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1149
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq1149
    | exact resolve eq1149 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1185 : (M.op x y) = (k x y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1144
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq1144
    | exact resolve eq1144 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1331 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (k X0 X0)
       have i₂ := eq274 X0 (k X0 X0)
       grind)
    | exact superpose eq274 eq13
    | (have r₁ := eq13 X0 (k X0 X0)
       have r₂ := eq274 X0 (k X0 X0)
       grind)
    | exact resolve eq13 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1344 : ∀ X0 X1 : G, (k X0 X0) = (k X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1331 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq1687 : ∀ X0 X2 : G, (σ (k X0 X0)) = (k X2 (σ (k X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq1344 X0 x
       have i₂ := eq341 X0 x
       grind)
    | exact superpose eq341 eq1344
    | exact resolve eq1344 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq1344
  have eq8313 : ∀ X0 : G, (σ (k (k X0 X0) y)) = (k (σ (k y y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq443 X0
       grind)
    | (have i₁ := eq41 (k x x)
       have i₂ := eq443 x
       grind)
    | exact superpose eq443 eq41
    | exact resolve eq41 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq8314 : ∀ X0 : G, (σ (k (k X0 X0) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8313 X0
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq8313
    | exact resolve eq8313 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8313
  have eq8332 : ∀ X0 : G, (σ (k (k X0 X0) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8314 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8314
    | (have j0 := eq8314 X0
       grind)
    | exact resolve eq8314 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8314
  have eq8338 : ∀ X0 : G, (k (σ (k X0 X0)) (σ y)) = (k (k (σ y) (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8332 X0
       have i₂ := eq41 (k X0 X0)
       grind)
    | exact superpose eq41 eq8332
    | exact resolve eq8332 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8332
  have eq11359 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1185
       grind)
    | exact superpose eq1185 eq41
    | exact resolve eq41 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1185
  have eq11360 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq11359
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11359
    | exact resolve eq11359 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11359
  have eq11362 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq20 eq11360
    | exact resolve eq11360 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11360
  have eq27869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq11362 eq1181
    | exact resolve eq1181 eq11362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq11362
  have eq27877 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq27869
       have r₂ := eq27
       grind)
    | exact resolve eq27869 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27869
  have eq27905 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq27877 eq347
    | exact resolve eq347 eq27877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq27877
  have eq28015 : y = (k y y) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq32 eq27905
    | exact resolve eq27905 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27905
  have eq28016 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq28015
  have eq28053 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq274 y x
       have i₂ := eq28016
       grind)
    | exact superpose eq28016 eq274
    | exact resolve eq274 eq28016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq28055 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq303 X0 y
       have i₂ := eq28016
       grind)
    | exact superpose eq28016 eq303
    | exact resolve eq303 eq28016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq28085 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1687 y x
       have i₂ := eq28016
       grind)
    | exact superpose eq28016 eq1687
    | exact resolve eq1687 eq28016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq28130 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8338 y
       have i₂ := eq28016
       grind)
    | exact superpose eq28016 eq8338
    | exact resolve eq8338 eq28016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8338 eq28016
  have eq28150 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28130
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28130
    | exact resolve eq28130 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28130
  have eq28189 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq28085 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28085
    | (have j0 := eq28085 X0
       grind)
    | exact resolve eq28085 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28085
  have eq28219 : y = (k y (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28055 eq28150
    | exact resolve eq28150 eq28055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28055 eq28150
  have eq28267 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq28189 eq28219
    | exact resolve eq28219 eq28189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28189 eq28219
  have eq28310 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq28267 eq32
    | exact resolve eq32 eq28267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28267
  have eq28338 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq30 eq28310
    | exact resolve eq28310 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28310
  have eq28339 : y = (σ y) ∨ x = y := by grind
  clear eq28338
  have eq28526 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq28053 x
       grind)
    | exact superpose eq28053 eq18
    | (have j1 := eq28053 x
       grind)
    | exact resolve eq18 eq28053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28053
  have eq28559 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28526 eq32
    | exact resolve eq32 eq28526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq28526
  have eq28593 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq28559
    | exact resolve eq28559 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28559
  have eq28594 : y = (M.op x y) ∨ x = y := by grind
  clear eq28593
  have eq28607 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq28594
       grind)
    | exact superpose eq28594 eq18
    | exact resolve eq18 eq28594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28608 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq28594
       grind)
    | exact superpose eq28594 eq24
    | exact resolve eq24 eq28594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28624 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq28339
       have i₂ := eq28594
       grind)
    | exact superpose eq28594 eq28339
    | exact resolve eq28339 eq28594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28339
  have eq28625 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq28594
  have eq28626 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq28624
       have r₂ := eq28625
       grind)
    | exact resolve eq28624 eq28625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28624 eq28625
  have eq28633 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq28608
    | exact resolve eq28608 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28608
  have eq28640 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq28626 eq28633
    | exact resolve eq28633 eq28626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28633
  have eq30046 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq28626 eq26
    | exact resolve eq26 eq28626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28626
  have eq30153 : ∀ X0 : G, (k X0 X0) = (M.op x (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28607 eq304
    | exact resolve eq304 eq28607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq30155 : (k x x) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq28607 eq192
    | exact resolve eq192 eq28607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq30173 : (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq28607 eq30155
    | exact resolve eq30155 eq28607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30155
  have eq30175 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28607 eq30153
    | exact resolve eq30153 eq28607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28607 eq30153
  have eq30688 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq220 x X0
       have i₂ := eq30173
       grind)
    | exact superpose eq30173 eq220
    | exact resolve eq220 eq30173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq30173
  have eq30868 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq30688
    | (have j0 := eq30688 X0
       grind)
    | exact resolve eq30688 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30688
  have eq30947 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30868 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30868
    | (have j0 := eq30868 X0
       grind)
    | exact resolve eq30868 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30868
  have eq31010 : ∀ X0 : G, (k X0 X0) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30947 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq30947
    | exact resolve eq30947 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30947
  have eq31059 : ∀ X0 : G, (k X0 X0) = (M.op (σ x) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28640 eq31010
    | exact resolve eq31010 eq28640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31010
  have eq31094 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30046 eq31059
    | exact resolve eq31059 eq30046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30046 eq31059
  have eq31120 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30175 eq31094
    | exact resolve eq31094 eq30175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30175 eq31094
  have eq31162 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31120 eq27
    | exact resolve eq27 eq31120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31120
  have eq31174 : x = y := by
    first
    | (have r₁ := eq31162
       have r₂ := eq28640
       grind)
    | exact resolve eq31162 eq28640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28640 eq31162
  have eq31512 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31174
       grind)
    | exact superpose eq31174 eq18
    | exact resolve eq18 eq31174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31513 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq31174
       grind)
    | exact superpose eq31174 eq24
    | exact resolve eq24 eq31174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31174
  have eq31527 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31513
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31513
    | exact resolve eq31513 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31513
  have eq31528 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq31512
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq31512
    | exact resolve eq31512 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31512
  have eq31530 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31527 eq26
    | exact resolve eq26 eq31527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq31527
  have eq31561 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq31530
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq31530
    | exact resolve eq31530 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq31530
  have eq31565 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq31528
       grind)
    | exact superpose eq31528 eq40
    | exact resolve eq40 eq31528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq31528
  have eq31734 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq31565
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31565
    | exact resolve eq31565 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31565
  have eq31785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31561 eq31734
    | exact resolve eq31734 eq31561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31561 eq31734
  have eq31821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq31785
    | exact resolve eq31785 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31785
  have eq31843 : False := by grind
  exact eq31843

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation3273 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3273 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq240 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 (M.op X0 X0)) ∨ X1 = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq58 X0 X2
       grind)
    | exact superpose eq58 eq12
    | (have j0 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ X1 = X2 := by
    intro X1 X2
    first
    | (have j0 := eq240 x X1 X2
       grind)
    | (have r₁ := eq240 x X1 X2
       have r₂ := eq58 x X1
       grind)
    | exact resolve eq240 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq240
  have eq1275 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq248 x y
       grind)
    | exact superpose eq248 eq49
    | (have j1 := eq248 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1293 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1275
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1275
    | exact resolve eq1275 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1294 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq1293
    | exact resolve eq1293 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1294 eq248
    | (have j0 := eq248 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq248 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq1294
  have eq1300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1298
    | exact resolve eq1298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1303 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1300
       have r₂ := eq28
       grind)
    | exact resolve eq1300 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1306 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1303 eq30
    | exact resolve eq30 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1303
  have eq1324 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1306
    | exact resolve eq1306 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1306
  have eq1325 : x = y := by grind
  clear eq1324
  have eq1328 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1325
       grind)
    | exact superpose eq1325 eq19
    | exact resolve eq19 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1329 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1325
       grind)
    | exact superpose eq1325 eq25
    | exact resolve eq25 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1325
  have eq1340 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1329
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1329
    | exact resolve eq1329 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1329
  have eq1343 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1340 eq27
    | exact resolve eq27 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1340
  have eq1391 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1343 eq71
    | exact resolve eq71 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1343
  have eq1411 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1391
       have i₂ := eq1328
       grind)
    | exact superpose eq1328 eq1391
    | exact resolve eq1391 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq1391
  have eq1486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1411 eq15
    | exact resolve eq15 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq1487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1486
    | exact resolve eq1486 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1486
  have eq1488 : False := by grind
  exact eq1488

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_y_Equation3273 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law3273 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq257 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 (M.op X0 X0)) ∨ X1 = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq58 X0 X2
       grind)
    | exact superpose eq58 eq12
    | (have j0 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ X1 = X2 := by
    intro X1 X2
    first
    | (have j0 := eq257 x X1 X2
       grind)
    | (have r₁ := eq257 x X1 X2
       have r₂ := eq58 x X1
       grind)
    | exact resolve eq257 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq257
  have eq1945 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq265 x y
       grind)
    | exact superpose eq265 eq49
    | (have j1 := eq265 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1961 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1945
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1945
    | exact resolve eq1945 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq1962 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq1961
    | exact resolve eq1961 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq1965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1962 eq265
    | (have j0 := eq265 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq265 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq1962
  have eq1966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1965
    | exact resolve eq1965 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1965
  have eq1969 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1966
       have r₂ := eq28
       grind)
    | exact resolve eq1966 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966
  have eq1972 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1969 eq30
    | exact resolve eq30 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1969
  have eq1990 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1972
    | exact resolve eq1972 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1972
  have eq1991 : x = y := by grind
  clear eq1990
  have eq1994 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1991
       grind)
    | exact superpose eq1991 eq19
    | exact resolve eq19 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1995 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1991
       grind)
    | exact superpose eq1991 eq25
    | exact resolve eq25 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1991
  have eq2006 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1995
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1995
    | exact resolve eq1995 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1995
  have eq2009 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2006 eq27
    | exact resolve eq27 eq2006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2006
  have eq2065 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2009 eq71
    | exact resolve eq71 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq2009
  have eq2089 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2065
       have i₂ := eq1994
       grind)
    | exact superpose eq1994 eq2065
    | exact resolve eq2065 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994 eq2065
  have eq2105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2089 eq15
    | exact resolve eq15 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq2106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2105
    | exact resolve eq2105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2105
  have eq2107 : False := by grind
  exact eq2107

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq722 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq729 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq722 X0 X1
       have j1 := eq58 X0 X1
       grind)
    | (have r₁ := eq722 X0 X1
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq722 X1 X1
       have r₂ := eq58 X1 X1
       grind)
    | exact resolve eq722 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq722
  have eq5646 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq729
  have eq5737 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5646 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5646
  have eq8138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5737 (σ X0) (σ X1)
       grind)
    | exact superpose eq5737 eq15
    | exact resolve eq15 eq5737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8151 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8138 X0 X1
       have i₂ := eq5737 X0 X1
       grind)
    | exact superpose eq5737 eq8138
    | exact resolve eq8138 eq5737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5737 eq8138
  have eq8163 : False := by grind
  exact eq8163

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq46 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq60
    | exact resolve eq60 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq60
  have eq84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq84
    | (have j0 := eq84 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq84 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq16
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq665 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq274
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq274
    | (have j1 := eq84 (σ x) (σ y)
       grind)
    | (have r₁ := eq274
       have r₂ := eq84 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq274
       have r₂ := eq84 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq274 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq274
  have eq668 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq665
  have eq671 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq668
       grind)
    | exact superpose eq668 eq16
    | exact resolve eq16 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq672 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq671
       have r₂ := eq69 x
       grind)
    | exact resolve eq671 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq713 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq672
       grind)
    | exact superpose eq672 eq10
    | exact resolve eq10 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq730 : x = y := by
    first
    | (have i₁ := eq713
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq713
    | exact resolve eq713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq779 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq730
       grind)
    | exact superpose eq730 eq16
    | exact resolve eq16 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq780 : False := by grind
  exact eq780

/-- `Equation3296`: `x ◇ x = y ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation3296 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3296 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3296.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq336 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1212 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1205 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1205
    | (have j0 := eq1205 X0 X1
       grind)
    | exact resolve eq1205 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq7940 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1212 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1212
    | (have j0 := eq1212 (σ X0) (σ X1)
       grind)
    | exact resolve eq1212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq7985 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7940 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq7940
    | (have j0 := eq7940 X0 X1
       grind)
    | exact resolve eq7940 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7940
  have eq602305 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (M.op (σ X0) (σ X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 (σ X0) (σ (σ X1))
       have i₂ := eq7985 X0 X1
       grind)
    | exact superpose eq7985 eq336
    | (have j0 := eq336 (σ X0) (σ (σ X1))
       have j1 := eq7985 X0 X1
       grind)
    | exact resolve eq336 eq7985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq602536 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7985 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7985
  have eq602540 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (M.op (σ X0) (σ X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq602305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602305
  have eq602754 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq602540 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq602540
    | (have j0 := eq602540 X0 X1
       grind)
    | exact resolve eq602540 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602540
  have eq602755 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq602754 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602754
  have eq603365 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (k (σ X0) (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq602755 X0 X1
       have i₂ := eq15 (σ X0) (σ X1)
       grind)
    | exact superpose eq15 eq602755
    | (have j0 := eq602755 X0 X1
       grind)
    | exact resolve eq602755 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602755
  have eq603771 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq603365 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq603365
    | (have j0 := eq603365 X0 X1
       grind)
    | exact resolve eq603365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603365
  have eq604008 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq603771 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq603771
    | (have j0 := eq603771 X0 X1
       grind)
    | exact resolve eq603771 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603771
  have eq604162 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq604008 X0 X1
       have j1 := eq602536 X0 X1
       grind)
    | (have r₁ := eq604008 X0 X1
       have r₂ := eq602536 X0 X1
       grind)
    | (have r₁ := eq604008 (M.op X0 X0) (k X0 X1)
       have r₂ := eq602536 X0 X1
       grind)
    | (have r₁ := eq604008 (k X0 X1) (M.op X0 X0)
       have r₂ := eq602536 X0 X1
       grind)
    | exact resolve eq604008 eq602536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602536 eq604008
  have eq1541247 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ X0)) = (σ (σ (k X1 (τ X0)))) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq604162 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq604162
    | exact resolve eq604162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604162
  have eq1542066 : ∀ X0 X1 : G, (σ (k (σ X1) X0)) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1541247 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1541247
    | (have j0 := eq1541247 X0 X1
       grind)
    | exact resolve eq1541247 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1541247
  have eq1542972 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1542066 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1542066
    | exact resolve eq1542066 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542066
  have eq1543544 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1542972 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq1542972
    | (have j0 := eq1542972 (τ X0) (τ X1)
       grind)
    | exact resolve eq1542972 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1543824 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1543544 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1543544
    | (have j0 := eq1543544 X0 X1
       grind)
    | exact resolve eq1543544 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543544
  have eq1543910 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1543824 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1543824
    | (have j0 := eq1543824 X0 X1
       grind)
    | exact resolve eq1543824 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543824
  have eq1543944 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1543910 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1543910
    | (have j0 := eq1543910 X0 X1
       grind)
    | exact resolve eq1543910 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543910
  have eq1543959 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1543944 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1543944
    | (have j0 := eq1543944 X0 X1
       grind)
    | exact resolve eq1543944 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543944
  have eq1543966 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1543959 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1543959
    | (have j0 := eq1543959 X0 X1
       grind)
    | exact resolve eq1543959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543959
  have eq1544083 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1542972 X0 X1
       have i₂ := eq1543966 X0 X1
       grind)
    | exact superpose eq1543966 eq1542972
    | (have j0 := eq1542972 X0 X1
       have j1 := eq1543966 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq1542972 eq1543966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542972 eq1543966
  have eq1554511 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1544083 x y
       grind)
    | exact superpose eq1544083 eq16
    | (have j1 := eq1544083 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1544083 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1544083 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1544083 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1544083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544083
  have eq1555033 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1554511
  have eq1555723 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1555033
       grind)
    | exact superpose eq1555033 eq10
    | exact resolve eq10 eq1555033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555033
  have eq1555963 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1555723
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1555723
    | exact resolve eq1555723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555723
  have eq1555964 : x = y := by grind
  clear eq1555963
  have eq1556002 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1555964
       grind)
    | exact superpose eq1555964 eq16
    | exact resolve eq16 eq1555964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555964
  have eq1556003 : False := by grind
  exact eq1556003

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation335 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law335 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  clear eq19
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq77 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1)
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq78 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq78 X0 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq78
    | exact resolve eq78 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq95 X0
       grind)
    | exact resolve eq12 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq116 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq130 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq119
    | (have j0 := eq119 X0
       grind)
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq119
  have eq131 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq130 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq130
    | (have j0 := eq130 X0
       grind)
    | exact resolve eq130 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq132 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq131 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq131 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq131 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq135 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq132 (σ X0)
       grind)
    | exact superpose eq132 eq15
    | exact resolve eq15 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq135 X0
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq135
    | exact resolve eq135 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq181 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq191 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq181
       have i₂ := eq146 y
       grind)
    | exact superpose eq146 eq181
    | exact resolve eq181 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq226 : ∀ X0 X1 : G, (σ (k X1 (k (τ (σ X0)) X0))) = (k (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X0 X1
       have i₂ := eq132 (σ X0)
       grind)
    | exact superpose eq132 eq22
    | exact resolve eq22 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq235 : ∀ X0 X1 : G, (σ (k X1 (k (τ (σ X0)) X0))) = (M.op (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq116 (σ X0) (σ X1)
       grind)
    | exact superpose eq116 eq226
    | exact resolve eq226 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq240 : ∀ X0 X1 : G, (σ (k X1 (k (τ (σ X0)) X0))) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq146 X0
       grind)
    | exact superpose eq146 eq235
    | exact resolve eq235 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq242 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (k X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq240
    | exact resolve eq240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq244 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 X1
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq242
    | exact resolve eq242 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq242
  have eq246 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq116 X0 X1
       grind)
    | exact superpose eq116 eq244
    | exact resolve eq244 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq244
  have eq1900 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq191
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq191
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq191
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq191
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq191 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq1901 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq1900
  have eq15955 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1901
       grind)
    | exact superpose eq1901 eq16
    | exact resolve eq16 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq15956 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq15955
       have r₂ := eq146 x
       grind)
    | exact resolve eq15955 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955
  have eq15958 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15956
       grind)
    | exact superpose eq15956 eq10
    | exact resolve eq10 eq15956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15956
  have eq16052 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15958
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15958
    | exact resolve eq15958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15958
  have eq16074 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16052
       grind)
    | exact superpose eq16052 eq16
    | exact resolve eq16 eq16052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16052
  have eq16075 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq16074
       have r₂ := eq146 x
       grind)
    | exact resolve eq16074 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq16074
  have eq16513 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq16075
       grind)
    | exact superpose eq16075 eq10
    | exact resolve eq10 eq16075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16075
  have eq16614 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16513
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq16513
    | exact resolve eq16513 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16513
  have eq16615 : y = (M.op y y) := by grind
  clear eq16614
  have eq16661 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq246 y x
       have i₂ := eq16615
       grind)
    | exact superpose eq16615 eq246
    | exact resolve eq246 eq16615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq16615
  have eq17543 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16661 x
       grind)
    | exact superpose eq16661 eq16
    | (have r₁ := eq16
       have r₂ := eq16661 x
       grind)
    | exact resolve eq16 eq16661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16661
  have eq17625 : False := by grind
  exact eq17625
