import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
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
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
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
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq63 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq63
    | exact resolve eq63 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq95 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq95
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq103
    | exact resolve eq103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq109
    | (have j0 := eq109 X0 X1
       grind)
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq119 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110 y x
       grind)
    | exact superpose eq110 eq16
    | (have j1 := eq110 y x
       grind)
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq297 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1 (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq97
    | exact resolve eq97 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq301 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (M.op X2 (τ (M.op X0 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq297 (M.op X0 X1) X2
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq297
    | exact resolve eq297 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq119
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq119
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq119
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq119
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq718 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq717
  have eq745 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq66
    | exact resolve eq66 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq66
  have eq3201 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301 X1 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq301
    | exact resolve eq301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq3390 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X1 (σ X0)))) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3201 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3201
    | exact resolve eq3201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201
  have eq6288 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X3 X1)) = (τ (τ (M.op X0 (M.op X0 (σ (σ X1)))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3390 X1 x X3
       have i₂ := eq3390 (σ X1) X0 x
       grind)
    | exact superpose eq3390 eq3390
    | exact resolve eq3390 eq3390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6325 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) = (τ (M.op X1 (M.op X1 (σ (σ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3390 (σ (M.op X0 X0)) X1 (σ X0)
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq3390
    | exact resolve eq3390 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq3390
  have eq6509 : ∀ X0 X1 : G, (σ X0) = (τ (M.op X1 (M.op X1 (σ (σ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6325 X0 X1
       have i₂ := eq745 X0
       grind)
    | exact superpose eq745 eq6325
    | exact resolve eq6325 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq6325
  have eq7752 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq718
       grind)
    | exact superpose eq718 eq16
    | exact resolve eq16 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq7753 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7752
       have r₂ := eq22 x
       grind)
    | exact resolve eq7752 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7752
  have eq307314 : ∀ X0 : G, (σ y) = (τ (M.op X0 (M.op X0 (σ (σ (M.op x x)))))) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq6509 y X0
       have i₂ := eq7753
       grind)
    | exact superpose eq7753 eq6509
    | exact resolve eq6509 eq7753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7753
  have eq307468 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq307314 x
       have i₂ := eq6509 x x
       grind)
    | exact superpose eq6509 eq307314
    | exact resolve eq307314 eq6509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307314
  have eq307469 : (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq307468
  have eq307500 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq307469
       grind)
    | exact superpose eq307469 eq22
    | exact resolve eq22 eq307469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307469
  have eq307900 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq307500
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq307500
    | exact resolve eq307500 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307500
  have eq307901 : (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq307900
  have eq308309 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op y y))) = (τ (τ (M.op X1 (M.op X1 (σ (σ (M.op x x))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6288 X1 (M.op y y) X0
       have i₂ := eq307901
       grind)
    | exact superpose eq307901 eq6288
    | exact resolve eq6288 eq307901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288 eq307901
  have eq308364 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op y y))) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq308309 X0 x
       have i₂ := eq6509 x x
       grind)
    | exact superpose eq6509 eq308309
    | exact resolve eq308309 eq6509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6509 eq308309
  have eq308604 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq308364 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq308364
    | exact resolve eq308364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308364
  have eq308643 : x = y := by
    first
    | (have i₁ := eq308604 x
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq308604
    | exact resolve eq308604 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq308604
  have eq308654 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq308643
       grind)
    | exact superpose eq308643 eq16
    | exact resolve eq16 eq308643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308643
  have eq308655 : False := by grind
  exact eq308655

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_x_pxy_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq50 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq53 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
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
  have eq56 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq50 eq16
    | exact resolve eq16 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq96 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq92
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq96
  have eq104 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq107 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq104
  have eq108 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq107
  have eq200 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq221 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq222 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X0) X1
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq232 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq221 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq221
    | exact resolve eq221 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq233 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq232
  have eq313 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq14 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq313 X0
       have i₂ := eq45 (M.op X0 X0)
       grind)
    | exact superpose eq45 eq313
    | exact resolve eq313 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq397 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq55 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq55
    | exact resolve eq55 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 X1
       have i₂ := eq55 (M.op X1 X1) X0
       grind)
    | exact superpose eq55 eq407
    | exact resolve eq407 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq411 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq404
       have i₂ := eq55 sF4 sF4
       grind)
    | exact superpose eq55 eq404
    | exact resolve eq404 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq413 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq401
       have i₂ := eq55 sF0 sF0
       grind)
    | exact superpose eq55 eq401
    | exact resolve eq401 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq414 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq399 X0
       have i₂ := eq45 (M.op X0 X0)
       grind)
    | exact superpose eq45 eq399
    | exact resolve eq399 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq416 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq397 X0 X1
       have i₂ := eq55 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq55 eq397
    | exact resolve eq397 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq417 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq55 X1 X1
       grind)
    | exact superpose eq55 eq409
    | exact resolve eq409 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq420 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq414 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq414
    | exact resolve eq414 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq422 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 X1
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq416
    | exact resolve eq416 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq423 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq406 X2 (M.op X0 X1)
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq406
    | exact resolve eq406 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq406
    | exact resolve eq406 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq498 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq16
    | exact resolve eq16 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (M.op (σ (k X0 X1)) (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X1) (σ X0)
       have i₂ := eq474 X0 X1
       grind)
    | exact superpose eq474 eq14
    | (have j1 := eq474 X0 X1
       grind)
    | exact resolve eq14 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq598 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (M.op (k X0 X1) (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq45 (k X0 X1)
       grind)
    | exact superpose eq45 eq595
    | (have j0 := eq595 X0 X1
       grind)
    | exact resolve eq595 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq595
  have eq736 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq411 eq55
    | exact resolve eq55 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq739 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq736
       have i₂ := eq55 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq55 eq736
    | exact resolve eq736 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq740 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq739
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq739
    | exact resolve eq739 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq741 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq740
       have i₂ := eq55 sF3 sF3
       grind)
    | exact superpose eq55 eq740
    | exact resolve eq740 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq751 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq413 eq55
    | exact resolve eq55 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq754 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq751
       have i₂ := eq55 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq55 eq751
    | exact resolve eq751 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq755 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq754
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq754
    | exact resolve eq754 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq756 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq755
       have i₂ := eq55 y y
       grind)
    | exact superpose eq55 eq755
    | exact resolve eq755 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq757 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq406 y y
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq406
    | exact resolve eq406 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1949 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq315
    | exact resolve eq315 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq2007 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1949 (M.op X0 X0)
       have i₂ := eq406 (M.op X0 X0) X0
       grind)
    | exact superpose eq406 eq1949
    | exact resolve eq1949 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq2101 : ∀ X0 : G, (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) = (M.op (σ (τ X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq420 (τ X0)
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq420
    | exact resolve eq420 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq2103 : (σ (M.op y (M.op y y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq420 y
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq420
    | exact resolve eq420 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq420
  have eq2114 : (M.op (σ y) (M.op (σ y) (σ y))) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq2103
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2103
    | exact resolve eq2103 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq2116 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq2101 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2101
    | exact resolve eq2101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2130 : (σ (M.op x (M.op x y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq2114
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq2114
    | exact resolve eq2114 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq2114
  have eq2131 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq2116 X0
       have i₂ := eq498 X0
       grind)
    | exact superpose eq498 eq2116
    | exact resolve eq2116 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq2116
  have eq2142 : (σ (M.op x (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq741 eq2130
    | exact resolve eq2130 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq2130
  have eq3014 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq417 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq417
    | exact resolve eq417 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3110 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3014 X0 X1
       have i₂ := eq406 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq406 eq3014
    | exact resolve eq3014 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014
  have eq3321 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq422 X0 X1
       grind)
    | exact superpose eq422 eq55
    | exact resolve eq55 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3324 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3321 X0 X1
       have i₂ := eq55 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq55 eq3321
    | exact resolve eq3321 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq3376 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3324 X0 X1
       have i₂ := eq55 (M.op X0 X0) X1
       grind)
    | exact superpose eq55 eq3324
    | exact resolve eq3324 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324
  have eq3419 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3376 X0 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq3376
    | exact resolve eq3376 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq3448 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3419 X0 X1
       have i₂ := eq417 X1 X0
       grind)
    | exact superpose eq417 eq3419
    | exact resolve eq3419 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq3419
  have eq3855 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3448 X1 X2
       have i₂ := eq3448 X1 X0
       grind)
    | (have i₁ := eq3448 X0 X1
       have i₂ := eq3448 X0 X0
       grind)
    | exact superpose eq3448 eq3448
    | exact resolve eq3448 eq3448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3448
  have eq4934 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ X0) (M.op (σ (k X0 (M.op x y))) (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq200 eq422
    | (have j1 := eq200 X0
       grind)
    | exact resolve eq422 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq422
  have eq4997 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq757 eq3855
    | exact resolve eq3855 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq3855
  have eq5695 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq222 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq222
    | exact resolve eq222 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq5777 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5695 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq5695
    | (have j0 := eq5695 X0 X1
       grind)
    | exact resolve eq5695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5695
  have eq7279 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (M.op (M.op X0 X1) (M.op X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq598 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq598
    | (have j0 := eq598 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | exact resolve eq598 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq7348 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (M.op X0 (M.op X1 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7279 X0 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq7279
    | (have j0 := eq7279 X0 X1
       grind)
    | exact resolve eq7279 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7279
  have eq597878 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53 eq7348
    | (have j0 := eq7348 x (M.op x y)
       grind)
    | exact resolve eq7348 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq7348
  have eq597989 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq597878
    | exact resolve eq597878 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597878
  have eq598055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq597989
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq597989
    | exact resolve eq597989 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597989
  have eq598112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq598055
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq598055
    | exact resolve eq598055 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598055
  have eq598149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq598112
    | exact resolve eq598112 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598112
  have eq598164 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq598149
       have r₂ := eq28
       grind)
    | exact resolve eq598149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598149
  have eq598170 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq598164
    | exact resolve eq598164 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598164
  have eq598173 : (M.op (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq598170
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq598170
    | exact resolve eq598170 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598170
  have eq598176 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108 eq598173
    | exact resolve eq598173 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq598173
  have eq598179 : (σ x) = (σ (M.op x y)) ∨ (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq598176
    | exact resolve eq598176 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598176
  have eq598181 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq598179
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq598179
    | exact resolve eq598179 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598179
  have eq598183 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq598181 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op x y))
       have r₂ := eq598181
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq598181
       grind)
    | exact resolve eq12 eq598181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598181
  have eq598210 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq598183
  have eq598211 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq598210
  have eq598317 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op x (M.op x y)))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq598211 eq3110
    | exact resolve eq3110 eq598211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598211
  have eq598343 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4997 eq598317
    | exact resolve eq598317 eq4997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598317
  have eq598465 : (τ (σ x)) = (k x (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq598343 eq66
    | exact resolve eq66 eq598343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq598343
  have eq598507 : (M.op x y) = (M.op y y) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq598465
    | exact resolve eq598465 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598465
  have eq600866 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56
       have i₂ := eq598507
       grind)
    | exact superpose eq598507 eq56
    | exact resolve eq56 eq598507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq598507
  have eq601042 : x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq600866
       have r₂ := eq12 x (M.op x y)
       grind)
    | exact resolve eq600866 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600866
  have eq601145 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq601042 eq4934
    | (have j0 := eq4934 x
       grind)
    | exact resolve eq4934 eq601042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4934
  have eq601159 : (σ x) = (σ (M.op x (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq601042 eq5777
    | (have j0 := eq5777 x (M.op x y)
       grind)
    | exact resolve eq5777 eq601042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5777 eq601042
  have eq601173 : (σ x) = (σ (M.op x (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq601159
  have eq601190 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2142 eq601173
    | exact resolve eq601173 eq2142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142 eq601173
  have eq601204 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq601145
       have i₂ := eq423 (σ x) sF1 (σ x)
       grind)
    | exact superpose eq423 eq601145
    | exact resolve eq601145 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq601145
  have eq601205 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq601204
  have eq601246 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq601190
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq601190
    | exact resolve eq601190 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601190
  have eq601259 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq601205
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq601205
    | exact resolve eq601205 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601205
  have eq601299 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq601259
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq601259
    | exact resolve eq601259 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601259
  have eq601300 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq601299
  have eq601514 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq601300 eq14
    | exact resolve eq14 eq601300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601300
  have eq601543 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq601514
       have i₂ := eq55 sF1 sF1
       grind)
    | exact superpose eq55 eq601514
    | exact resolve eq601514 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601514
  have eq661960 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq601246 eq3110
    | exact resolve eq3110 eq601246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110 eq601246
  have eq661986 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4997 eq661960
    | exact resolve eq661960 eq4997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661960
  have eq662359 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq661986 eq55
    | exact resolve eq55 eq661986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq661986
  have eq662604 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq54 eq662359
    | exact resolve eq662359 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq662359
  have eq664090 : (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) (τ (σ y)))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq662604 eq2131
    | exact resolve eq2131 eq662604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131 eq662604
  have eq664243 : (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30 eq664090
    | exact resolve eq664090 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq664090
  have eq664278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq664243
    | exact resolve eq664243 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664243
  have eq664287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq664278
    | exact resolve eq664278 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664278
  have eq664292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq664287
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq664287
    | exact resolve eq664287 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq664287
  have eq664296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq664292
    | exact resolve eq664292 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664292
  have eq664299 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq664296
       have r₂ := eq28
       grind)
    | exact resolve eq664296 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664296
  have eq664330 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq424 y X0
       have i₂ := eq664299
       grind)
    | exact superpose eq664299 eq424
    | exact resolve eq424 eq664299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq664299
  have eq664479 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq21 eq664330
    | (have j0 := eq664330 X0
       grind)
    | exact resolve eq664330 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664330
  have eq664526 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq664479 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq664479
    | (have j0 := eq664479 X0
       grind)
    | exact resolve eq664479 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664479
  have eq674006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq664526 eq601543
    | exact resolve eq601543 eq664526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601543 eq664526
  have eq674008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq674006
  have eq674028 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq674008
    | exact resolve eq674008 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674008
  have eq674080 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq674028
       have r₂ := eq28
       grind)
    | exact resolve eq674028 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674028
  have eq674107 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq674080 eq29
    | exact resolve eq29 eq674080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq674080
  have eq674515 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq674107
    | exact resolve eq674107 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq674107
  have eq674516 : x = (M.op x y) := by grind
  clear eq674515
  have eq674539 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq674516 eq21
    | exact resolve eq21 eq674516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq674733 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x x))) := by
    intro X0
    first
    | exact superpose eq674516 eq4997
    | exact resolve eq4997 eq674516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4997 eq674516
  have eq674832 : x = (M.op y y) := by
    first
    | (have i₁ := eq674733 x
       have i₂ := eq406 x x
       grind)
    | exact superpose eq406 eq674733
    | exact resolve eq674733 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq674733
  have eq675000 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq674539
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq674539
    | exact resolve eq674539 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674539
  have eq680415 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2007 y
       have i₂ := eq674832
       grind)
    | exact superpose eq674832 eq2007
    | exact resolve eq2007 eq674832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007 eq674832
  have eq680569 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq680415
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq680415
    | exact resolve eq680415 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq680415
  have eq680634 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq680569
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq680569
    | exact resolve eq680569 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq680569
  have eq680684 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq680634
    | exact resolve eq680634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq680634
  have eq680717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq675000 eq680684
    | exact resolve eq680684 eq675000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675000 eq680684
  have eq680744 : False := by grind
  exact eq680744

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pxy_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq53 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
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
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq80
    | exact resolve eq80 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq96 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq92
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq96
  have eq401 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq55 X1 X1
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq404
       have i₂ := eq55 sF4 sF4
       grind)
    | exact superpose eq55 eq404
    | exact resolve eq404 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq413 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq401
       have i₂ := eq55 sF0 sF0
       grind)
    | exact superpose eq55 eq401
    | exact resolve eq401 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq474 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq72
  have eq573 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq474 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq474
    | (have j0 := eq474 x X0
       grind)
    | exact resolve eq474 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq736 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq411 eq55
    | exact resolve eq55 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq736
       have i₂ := eq55 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq55 eq736
    | exact resolve eq736 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq740 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq739
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq739
    | exact resolve eq739 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq741 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq740
       have i₂ := eq55 sF3 sF3
       grind)
    | exact superpose eq55 eq740
    | exact resolve eq740 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq742 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq741 eq406
    | exact resolve eq406 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq751 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq413 eq55
    | exact resolve eq55 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq751
       have i₂ := eq55 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq55 eq751
    | exact resolve eq751 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq755 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq754
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq754
    | exact resolve eq754 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq756 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq755
       have i₂ := eq55 y y
       grind)
    | exact superpose eq55 eq755
    | exact resolve eq755 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq757 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq406 y y
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq406
    | exact resolve eq406 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq5865 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq573 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq573
    | (have j0 := eq573 y
       grind)
    | exact resolve eq573 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq5899 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5865
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq5865
    | exact resolve eq5865 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5865
  have eq5927 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5899
    | exact resolve eq5899 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5899
  have eq5939 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5927
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq5927
    | exact resolve eq5927 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5927
  have eq5944 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5939
    | exact resolve eq5939 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5939
  have eq6956 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq408 X1 (M.op X0 X0) X1
       have i₂ := eq406 X1 X0
       grind)
    | exact superpose eq406 eq408
    | (have j0 := eq408 X1 (M.op X0 X0) X1
       grind)
    | exact resolve eq408 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq408
  have eq7008 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6956 X0 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq6956
    | (have j0 := eq6956 X0 X1
       grind)
    | exact resolve eq6956 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq6956
  have eq11327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq83 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq11327
    | exact resolve eq11327 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11327
  have eq11334 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq11328
       have r₂ := eq28
       grind)
    | exact resolve eq11328 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11328
  have eq11336 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq11334
    | exact resolve eq11334 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11334
  have eq315973 : (M.op x y) ≠ (M.op y y) ∨ x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ (M.op x (M.op (M.op x y) (M.op x y))) = (k x (M.op x (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq413 eq7008
    | (have j0 := eq7008 (M.op x y) x
       grind)
    | exact resolve eq7008 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq315976 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq411 eq7008
    | (have j0 := eq7008 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq7008 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq7008
  have eq315992 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq54 eq315976
    | exact resolve eq315976 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315976
  have eq315995 : x = y ∨ (M.op x y) ≠ (M.op y y) ∨ (M.op x (M.op (M.op x y) (M.op x y))) = (k x (M.op x (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq53 eq315973
    | exact resolve eq315973 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315973
  have eq316056 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq54 eq315992
    | exact resolve eq315992 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq315992
  have eq316059 : (M.op x y) ≠ (M.op y y) ∨ x = y ∨ y = (k x y) := by
    first
    | exact superpose eq53 eq315995
    | exact resolve eq315995 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq315995
  have eq1431477 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq11336 eq316056
    | (have r₁ := eq316056
       have r₂ := eq11336
       grind)
    | exact resolve eq316056 eq11336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11336 eq316056
  have eq1431509 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq1431477
  have eq1431510 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq1431509
  have eq1431520 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq1431510 eq61
    | exact resolve eq61 eq1431510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1431521 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq1431510 eq83
    | exact resolve eq83 eq1431510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1431510
  have eq1431594 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1431521
  have eq1431626 : y = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq1431520
    | exact resolve eq1431520 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431520
  have eq1431641 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq1431594
       grind)
    | exact superpose eq1431594 eq97
    | exact resolve eq97 eq1431594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431594
  have eq1431903 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq1431641
    | exact resolve eq1431641 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431641
  have eq1436490 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1431626
       have r₂ := eq316059
       grind)
    | exact resolve eq1431626 eq316059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316059 eq1431626
  have eq1436494 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq1436490
       grind)
    | exact superpose eq1436490 eq49
    | exact resolve eq49 eq1436490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1436490
  have eq1436689 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1436494
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1436494
    | exact resolve eq1436494 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436494
  have eq1437484 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1436689 eq5944
    | exact resolve eq5944 eq1436689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5944 eq1436689
  have eq1437547 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1437484
  have eq1438269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1437547 eq1431903
    | exact resolve eq1431903 eq1437547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1438421 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1438269
  have eq1438560 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1438421
       have r₂ := eq28
       grind)
    | exact resolve eq1438421 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438421
  have eq1438635 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1438560 eq742
    | exact resolve eq742 eq1438560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq1440998 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq1438635
    | exact resolve eq1438635 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438635
  have eq1448085 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1438560 eq1440998
    | exact resolve eq1440998 eq1438560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438560 eq1440998
  have eq1448808 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1448085
  have eq1451340 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1448808 eq1431903
    | exact resolve eq1431903 eq1448808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431903 eq1448808
  have eq1451492 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1451340
  have eq1451786 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1451492 eq30
    | exact resolve eq30 eq1451492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452293 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq1451786
    | exact resolve eq1451786 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451786
  have eq1452294 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1452293
  have eq1452331 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1452294 eq30
    | exact resolve eq30 eq1452294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452294
  have eq1454358 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1452331
    | exact resolve eq1452331 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1452331
  have eq1454462 : y = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1454358 eq757
    | exact resolve eq757 eq1454358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq1455533 : y = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1454462
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1454462
    | exact resolve eq1454462 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454462
  have eq1455748 : y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1454358 eq1455533
    | exact resolve eq1455533 eq1454358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454358 eq1455533
  have eq1455860 : y = (M.op y y) ∨ x = y := by grind
  clear eq1455748
  have eq1459580 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq1455860
       grind)
    | exact superpose eq1455860 eq97
    | exact resolve eq97 eq1455860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1455860
  have eq1459986 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1459580
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1459580
    | exact resolve eq1459580 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459580
  have eq1462493 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1459986 eq1437547
    | exact resolve eq1437547 eq1459986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437547 eq1459986
  have eq1462641 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1462493
  have eq1481219 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1462641 eq28
    | exact resolve eq28 eq1462641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462641
  have eq1484545 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1481219
       have r₂ := eq1451492
       grind)
    | exact resolve eq1481219 eq1451492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451492 eq1481219
  have eq1485369 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1484545 eq30
    | exact resolve eq30 eq1484545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1484545
  have eq1485891 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1485369
    | exact resolve eq1485369 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1485369
  have eq1485892 : x = y := by grind
  clear eq1485891
  have eq1485927 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1485892
       grind)
    | exact superpose eq1485892 eq19
    | exact resolve eq19 eq1485892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1485928 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1485892
       grind)
    | exact superpose eq1485892 eq25
    | exact resolve eq25 eq1485892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1485892
  have eq1486529 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1485928
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1485928
    | exact resolve eq1485928 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1485928
  have eq1486571 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1486529 eq27
    | exact resolve eq27 eq1486529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1486529
  have eq1487851 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1486571 eq70
    | exact resolve eq70 eq1486571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1486571
  have eq1488052 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1487851
       have i₂ := eq1485927
       grind)
    | exact superpose eq1485927 eq1487851
    | exact resolve eq1487851 eq1485927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485927 eq1487851
  have eq1488344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1488052 eq15
    | exact resolve eq15 eq1488052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488052
  have eq1489118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1488344
    | exact resolve eq1488344 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1488344
  have eq1489292 : False := by grind
  exact eq1489292

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq42 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq59 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq62
    | exact resolve eq62 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq60
    | exact resolve eq60 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq65 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq59
    | exact resolve eq59 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq63
    | exact resolve eq63 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq68 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq64
    | exact resolve eq64 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq69 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq65
    | exact resolve eq65 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X1)) = (σ (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq31
    | (have j0 := eq31 (σ X1) (σ X0)
       grind)
    | exact resolve eq31 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq101 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X2 (M.op X0 X1)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq61
    | exact resolve eq61 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq61 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq61 (M.op X0 X0) X0
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq158 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq102 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq102
    | exact resolve eq102 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq190 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1)))) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq69 (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq69
    | exact resolve eq69 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq199 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X1 X1)))) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq190
    | exact resolve eq190 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq388 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 (M.op X0 (M.op X1 X1))
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq67
    | exact resolve eq67 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq417 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq101 X1 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq101 eq388
    | exact resolve eq388 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq427 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) = (M.op X0 (M.op X1 (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 (M.op X1 (M.op X0 X0))
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq68
    | exact resolve eq68 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq472 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X1
       have i₂ := eq9 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq427
    | exact resolve eq427 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq492 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq472 X0 X1
       have i₂ := eq101 X1 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq101 eq472
    | exact resolve eq472 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq543 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42
    | exact resolve eq42 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq563 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq543 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq543
    | (have j0 := eq543 X0 X1
       grind)
    | exact resolve eq543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq994 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq72 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq72 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq72 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1012 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq994
  have eq1090 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X1 X0))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X1)) = (σ (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1233 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq16
    | exact resolve eq16 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1012
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1012
       grind)
    | exact resolve eq13 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1240 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq417 (σ y) (σ x)
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq417
    | exact resolve eq417 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1243 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1235
  have eq1244 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1243
  have eq1250 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1244
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1244
    | exact resolve eq1244 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1255 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1250
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq1250
    | exact resolve eq1250 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq1409 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X2 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq492 (M.op X0 X1) X2
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq492
    | exact resolve eq492 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq492
  have eq3355 : ∀ X0 X1 : G, (σ (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))))) = (M.op (σ (M.op X1 (M.op X1 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X1 (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq199
    | exact resolve eq199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq3411 : ∀ X0 X1 : G, (M.op (σ (M.op X1 (M.op X1 X0))) (σ X0)) = (σ (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3355 X0 X1
       have i₂ := eq1409 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq1409 eq3355
    | exact resolve eq3355 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq3355
  have eq3465 : ∀ X0 X1 : G, (M.op (σ (M.op X1 (M.op X1 X0))) (σ X0)) = (σ (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3411 X0 X1
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq3411
    | exact resolve eq3411 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq3411
  have eq3511 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X1 (M.op X1 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3465 X0 X1
       have i₂ := eq101 X0 X0 X1
       grind)
    | exact superpose eq101 eq3465
    | exact resolve eq3465 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq3465
  have eq3838 : (σ (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq563 x y
       have i₂ := eq1255
       grind)
    | exact superpose eq1255 eq563
    | (have j0 := eq563 x y
       grind)
    | exact resolve eq563 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq3840 : (k y x) = (τ (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1255
       grind)
    | exact superpose eq1255 eq10
    | exact resolve eq10 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq3862 : (σ (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq3838
  have eq3871 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3840
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq3840
    | exact resolve eq3840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3840
  have eq3873 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 (k y x) (M.op y y)
       grind)
    | (have r₁ := eq3871
       have r₂ := eq13 y x
       grind)
    | exact resolve eq3871 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871
  have eq12718 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1090 (τ X1) (τ X0)
       have i₂ := eq110 X1 X0
       grind)
    | exact superpose eq110 eq1090
    | (have j0 := eq1090 (τ X1) (τ X0)
       grind)
    | exact resolve eq1090 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq1090
  have eq12793 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12718 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq12718
    | (have j0 := eq12718 X0 X1
       grind)
    | exact resolve eq12718 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12718
  have eq12836 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12793 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12793
    | (have j0 := eq12793 X0 X1
       grind)
    | exact resolve eq12793 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12793
  have eq12870 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12836 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12836
    | (have j0 := eq12836 X0 X1
       grind)
    | exact resolve eq12836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12836
  have eq12893 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12870 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq12870
    | (have j0 := eq12870 X0 X1
       grind)
    | exact resolve eq12870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12870
  have eq12913 : ∀ X0 X1 : G, (σ X1) = (σ (σ (τ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12893 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq12893
    | (have j0 := eq12893 X0 X1
       grind)
    | exact resolve eq12893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12893
  have eq12930 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12913 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12913
    | (have j0 := eq12913 X0 X1
       grind)
    | exact resolve eq12913 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12913
  have eq72977 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1240
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq1240
    | exact resolve eq1240 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq1240
  have eq73003 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq72977
  have eq73015 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq73003
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq73003
    | exact resolve eq73003 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73003
  have eq84963 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3862
       have i₂ := eq73015
       grind)
    | exact superpose eq73015 eq3862
    | exact resolve eq3862 eq73015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3862 eq73015
  have eq85163 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq84963
  have eq85192 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq85163
       have r₂ := eq1233
       grind)
    | exact resolve eq85163 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233 eq85163
  have eq97166 : y = (M.op y (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq417 y x
       have i₂ := eq85192
       grind)
    | exact superpose eq85192 eq417
    | exact resolve eq417 eq85192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq113297 : y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97166
       have i₂ := eq85192
       grind)
    | exact superpose eq85192 eq97166
    | exact resolve eq97166 eq85192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97166
  have eq113322 : y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq113297
  have eq121448 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3511 y y
       have i₂ := eq113322
       grind)
    | exact superpose eq113322 eq3511
    | exact resolve eq3511 eq113322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3511 eq113322
  have eq121465 : (σ y) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq121448
       have i₂ := eq158 y
       grind)
    | exact superpose eq158 eq121448
    | exact resolve eq121448 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq121448
  have eq160037 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12930 y x
       have i₂ := eq3873
       grind)
    | exact superpose eq3873 eq12930
    | (have j0 := eq12930 y x
       grind)
    | exact resolve eq12930 eq3873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3873 eq12930
  have eq160116 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq160037
  have eq160154 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq160116
       have r₂ := eq121465
       grind)
    | exact resolve eq160116 eq121465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121465 eq160116
  have eq182429 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq160154
       grind)
    | exact superpose eq160154 eq16
    | exact resolve eq16 eq160154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160154
  have eq196381 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq182429
       have i₂ := eq85192
       grind)
    | exact superpose eq85192 eq182429
    | exact resolve eq182429 eq85192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85192 eq182429
  have eq196382 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq196381
  have eq196383 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq196382
  have eq208212 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq196383
       grind)
    | exact superpose eq196383 eq10
    | exact resolve eq10 eq196383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196383
  have eq208449 : x = y ∨ x = y := by
    first
    | (have i₁ := eq208212
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq208212
    | exact resolve eq208212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208212
  have eq208450 : x = y := by grind
  clear eq208449
  have eq223022 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq208450
       grind)
    | exact superpose eq208450 eq16
    | exact resolve eq16 eq208450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208450
  have eq223023 : False := by grind
  exact eq223023

/-- `Equation934`: `x = y ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_y_pxy_x_pyx_Equation934 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law934 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law934.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X2) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  clear eq36
  have eq51 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op y X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 (M.op (M.op X1 X2) (M.op X2 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X3 X0)) = (M.op X1 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X3) (M.op X3 X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
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
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq44
    | exact resolve eq44 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
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
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq103 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq105 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq104
    | exact resolve eq104 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq108
    | exact resolve eq108 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq103
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq118
    | exact resolve eq118 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq119
    | exact resolve eq119 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq121 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq105
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq66 sF1
       grind)
    | exact superpose eq66 eq136
    | exact resolve eq136 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq141 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq66 sF0
       grind)
    | exact superpose eq66 eq139
    | exact resolve eq139 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq148 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op y X1) (M.op X1 X0)) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op y X1) (M.op X1 X0))
       have i₂ := eq14 X0 y X1
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X0)) = (M.op X1 (M.op (M.op X1 x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op (M.op (M.op x y) (M.op y X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (M.op X1 X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op sF3 x) (M.op x X0))
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op X1 (M.op (M.op X1 (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op (M.op X1 x) (M.op x y)) = (M.op X0 (M.op (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (M.op (M.op y x) (M.op x y)) = (M.op x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X0 X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : (M.op (M.op y (σ x)) (M.op (σ x) (σ y))) = (M.op x (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 X3) (M.op X3 X0)) (M.op (M.op (M.op X1 X2) X0) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X2 X3) (M.op X3 X0)) X1 X2 X4
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X4) (M.op X4 X0)) = (M.op X1 (M.op X2 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X2 X1 X3 (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X4) (M.op X4 X0))
       have i₂ := eq14 X0 (M.op (M.op X1 X3) (M.op X3 X2)) X4
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X2) (M.op X2 X1)) (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 X0)) = (M.op X4 (M.op (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X5) (M.op X5 X4)) X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X2 X1 X3 (M.op X4 (M.op (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X5) (M.op X5 X4)) X0))
       have i₂ := eq53 X4 (M.op (M.op X1 X3) (M.op X3 X2)) X5 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X2) X1 X2 (M.op (M.op X2 (M.op X1 X2)) X0)
       have i₂ := eq14 X0 (M.op X1 X2) (M.op X2 (M.op X1 X2))
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X4) (M.op X4 (M.op (M.op X1 X3) (M.op X3 X2)))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X2 X1 X3 (M.op (M.op (M.op X2 X4) (M.op X4 (M.op (M.op X1 X3) (M.op X3 X2)))) X0)
       have i₂ := eq53 (M.op (M.op X1 X3) (M.op X3 X2)) X2 X4 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X1 X2) X0)) = (M.op X3 (M.op (M.op (M.op X2 X4) (M.op X4 X3)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X3 (M.op (M.op (M.op X2 X4) (M.op X4 X3)) X0)) X1 X2
       have i₂ := eq53 X3 X2 X4 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X2) X3) (M.op X3 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op (M.op (M.op X1 X2) X3) (M.op X3 X2)) X0) X1 X2
       have i₂ := eq53 X2 (M.op X1 X2) X3 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op (M.op y X2) (M.op X2 X1)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X1 (M.op (M.op (M.op y X2) (M.op X2 X1)) X0))
       have i₂ := eq53 X1 y X2 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X1) (M.op X1 y)) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op (M.op sF0 x) (M.op x y)) x)
       have i₂ := eq53 y sF0 x x
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op (M.op (σ y) X2) (M.op X2 X1)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 (M.op (M.op (M.op sF3 X2) (M.op X2 X0)) x))
       have i₂ := eq53 X0 sF3 X2 x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X1 (σ y))) X0) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op (M.op sF4 x) (M.op x sF3)) x)
       have i₂ := eq53 sF3 sF4 x x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq141 eq73
    | exact resolve eq73 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X4 (M.op (M.op X4 X1) (M.op (M.op X2 X3) (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op (M.op X2 X3) (M.op X3 X0)) X4 X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op X2 (M.op (M.op X2 X0) (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op (M.op X5 X3) (M.op X4 X2))) = (M.op (M.op X3 (M.op X1 X4)) (M.op X0 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 (M.op X4 X2) X5 X3 (M.op X1 X4)
       have i₂ := eq56 X2 X0 X1 X4
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X0 X1) X2)) = (M.op X4 (M.op (M.op X4 X1) X2)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq56 X2 X4 X1 x
       have i₂ := eq56 X2 X0 X1 x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X1 X0) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X4))) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53 X2 X1 x X4
       have i₂ := eq56 X2 X0 X1 x
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq56 X2 X0 X1 x
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X4) X3) = (M.op X1 (M.op X4 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X1 X2 (M.op (M.op X2 X4) X3)
       have i₂ := eq56 X3 X0 (M.op X1 X2) (M.op X2 X4)
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X2) = (M.op X3 (M.op (M.op X3 (M.op X1 X4)) (M.op X0 (M.op (M.op X0 X1) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X4 X2) X3 (M.op X1 X4)
       have i₂ := eq56 X2 X0 X1 X4
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq590 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq590
    | (have j0 := eq590 y
       grind)
    | exact resolve eq590 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq591
    | (have j0 := eq591 (σ y)
       grind)
    | exact resolve eq591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq591 eq14
    | exact resolve eq14 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X1) (M.op X1 X2)) = (M.op (M.op (σ x) X0) (M.op (σ y) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq591 eq56
    | exact resolve eq56 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ x) X1)) (σ y)) = (M.op X2 (M.op (M.op X2 X0) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq591 eq56
    | exact resolve eq56 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq993 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq88
  have eq1091 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq993 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq993 X0 X1
       grind)
    | exact superpose eq993 eq13
    | (have j1 := eq993 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq993 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq993 X0 X1
       grind)
    | exact resolve eq13 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1103 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1091 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1103 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq1103
    | (have j0 := eq1103 X0 X1
       grind)
    | exact resolve eq1103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1160 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op X0 (M.op y x)) (M.op x (M.op (M.op x y) y)))) := by
    intro X0
    first
    | exact superpose eq248 eq14
    | exact resolve eq14 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq1199 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X0 (M.op y (σ x))) (M.op x (M.op (M.op x y) (σ y))))) := by
    intro X0
    first
    | exact superpose eq253 eq14
    | exact resolve eq14 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq1211 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X0 (M.op (σ y) (σ x))) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    intro X0
    first
    | exact superpose eq254 eq14
    | exact resolve eq14 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1245 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) X1) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq591 eq478
    | exact resolve eq478 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1247 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq254 eq478
    | exact resolve eq478 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1252 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq478 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq478
    | (have j0 := eq478 X0 x y
       grind)
    | exact resolve eq478 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1257 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq478
    | (have j0 := eq478 X0 (σ x) (σ y)
       grind)
    | exact resolve eq478 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq478 X2 (M.op (M.op X1 X0) X1) (M.op X1 X0)
       have i₂ := eq14 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq478
    | exact resolve eq478 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1265 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq54 eq478
    | exact resolve eq478 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1279 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) (M.op X3 X1)) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X1 X2 (M.op X0 X2) X3
       have i₂ := eq478 X1 X0 X2
       grind)
    | exact superpose eq478 eq56
    | exact resolve eq56 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1379 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq588
    | (have j0 := eq588 X0 (σ x) (σ y)
       grind)
    | exact resolve eq588 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq588
    | exact resolve eq588 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1411 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq588
    | exact resolve eq588 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1414 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq641 eq588
    | exact resolve eq588 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq55 eq588
    | exact resolve eq588 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1431 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq614 eq588
    | exact resolve eq588 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq641 eq588
    | exact resolve eq588 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1445 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X0)) = (M.op X1 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X3 (M.op X2 X0)) X1 (M.op X2 X3)
       have i₂ := eq588 X0 X2 X3
       grind)
    | exact superpose eq588 eq14
    | exact resolve eq14 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op (M.op X2 (M.op X1 X0)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq478 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq588 X0 X1 X2
       grind)
    | exact superpose eq588 eq478
    | exact resolve eq478 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1466 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 (M.op y (M.op x y))) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1431 eq14
    | exact resolve eq14 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq1479 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1435 eq14
    | exact resolve eq14 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq1534 : y = (M.op (M.op x (M.op y (M.op x y))) (M.op x (M.op x y))) := by
    first
    | exact superpose eq1252 eq590
    | exact resolve eq590 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1536 : (σ y) = (M.op (M.op (σ x) (M.op y (M.op x y))) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1252 eq591
    | exact resolve eq591 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1599 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y X0)) (M.op x (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq594
    | exact resolve eq594 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1625 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op (M.op X1 X0) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq594
    | exact resolve eq594 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1733 : (σ y) = (M.op (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1257 eq591
    | exact resolve eq591 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2127 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) (σ y)) := by
    first
    | exact superpose eq1257 eq1419
    | exact resolve eq1419 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257 eq1419
  have eq2194 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y X0)) X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq478 X1 (M.op X0 x) X0
       have i₂ := eq240 X0 X0
       grind)
    | exact superpose eq240 eq478
    | exact resolve eq478 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2384 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))))) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq55 eq242
    | exact resolve eq242 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq2401 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y))))) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq591 eq242
    | exact resolve eq242 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2516 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1) = (M.op (M.op X0 (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq243 eq478
    | exact resolve eq478 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2536 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (σ x)) X0) = (M.op X1 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq243 eq594
    | exact resolve eq594 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2603 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 X0)) = (M.op (M.op (σ y) X1) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 (M.op (M.op sF3 X0) (M.op sF4 X0))
       have i₂ := eq588 X0 sF4 (M.op sF3 X0)
       grind)
    | exact superpose eq588 eq244
    | exact resolve eq244 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3215 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq243 eq251
    | exact resolve eq251 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3228 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X1) = (M.op (M.op (σ y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq251 eq478
    | exact resolve eq478 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3559 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (σ x)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 (M.op sF4 (M.op (M.op X0 sF2) X0))
       have i₂ := eq588 X0 (M.op X0 sF2) sF4
       grind)
    | exact superpose eq588 eq252
    | exact resolve eq252 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq4106 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) X2)) = (M.op (σ x) (M.op (M.op X1 (σ y)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq486 (M.op (M.op X1 sF3) X0) X1
       have i₂ := eq56 X0 X1 (M.op sF4 X1) (M.op X1 sF3)
       grind)
    | exact superpose eq56 eq486
    | exact resolve eq486 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq4125 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op (σ x) X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq486 eq594
    | exact resolve eq594 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7195 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1466 (M.op (M.op x sF0) y)
       have i₂ := eq482 sF0 x sF0 y
       grind)
    | exact superpose eq482 eq1466
    | exact resolve eq1466 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq7197 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1479 (M.op (M.op x sF4) sF3)
       have i₂ := eq482 sF4 x sF4 sF3
       grind)
    | exact superpose eq482 eq1479
    | exact resolve eq1479 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq1479
  have eq7414 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq7195 (M.op sF0 X0)
       have i₂ := eq1262 X0 sF0 y
       grind)
    | exact superpose eq1262 eq7195
    | exact resolve eq7195 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7195
  have eq7473 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq7197 (M.op sF4 X0)
       have i₂ := eq1262 X0 sF4 sF3
       grind)
    | exact superpose eq1262 eq7197
    | exact resolve eq7197 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7197
  have eq8073 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 X1) X2))) = (M.op (M.op (σ y) X3) (M.op X0 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq242 (M.op (M.op X3 X1) X2) X3
       have i₂ := eq571 X3 X1 X2 X0
       grind)
    | (have i₁ := eq242 (M.op (M.op X3 X1) X2) X3
       have i₂ := eq571 X0 X1 X2 X3
       grind)
    | exact superpose eq571 eq242
    | exact resolve eq242 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq8509 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq7473 eq594
    | exact resolve eq594 eq7473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9526 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (σ y))))) := by
    intro X0
    first
    | exact superpose eq8509 eq594
    | exact resolve eq594 eq8509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9821 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X3 X1) X2) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq593 X3 X1 X2 (M.op (M.op (M.op X3 X1) X2) (M.op X3 X0))
       have i₂ := eq588 X0 X3 (M.op (M.op X3 X1) X2)
       grind)
    | exact superpose eq588 eq593
    | exact resolve eq593 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9827 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op (M.op (σ x) X0) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq591 eq593
    | exact resolve eq593 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq14808 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X1 (σ y))) = (M.op (M.op (M.op (σ x) (M.op (M.op X0 (σ y)) X1)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq486 eq476
    | exact resolve eq476 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq14908 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X1 (σ y))) = (M.op (M.op (M.op X0 (σ y)) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14808 X0 X1
       have i₂ := eq1262 (M.op (M.op X0 sF3) X1) sF2 sF4
       grind)
    | exact superpose eq1262 eq14808
    | exact resolve eq14808 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14808
  have eq15035 : ∀ X0 X1 : G, (M.op x (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op x (M.op (M.op x y) X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq483 X0 X1 x
       have i₂ := eq239 X1 x
       grind)
    | exact superpose eq239 eq483
    | exact resolve eq483 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq15450 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq242 eq485
    | exact resolve eq485 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq485
  have eq15589 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) (σ x)) X0))) := by
    intro X0 X1
    first
    | exact superpose eq243 eq15450
    | exact resolve eq15450 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15767 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15589 x X1
       have i₂ := eq1262 (M.op sF4 X1) sF2 x
       grind)
    | exact superpose eq1262 eq15589
    | exact resolve eq15589 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15589
  have eq18354 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op X1 (M.op (M.op X1 X0) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq254 eq562
    | exact resolve eq562 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22123 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (M.op (M.op X2 (σ X1)) (σ (k X0 X1)))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X2 (σ X1)
       have i₂ := eq1109 X1 X0
       grind)
    | exact superpose eq1109 eq14
    | (have j1 := eq1109 X1 X0
       grind)
    | exact resolve eq14 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq24094 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (M.op X1 X0) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq562 eq463
    | exact resolve eq463 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq562
  have eq26211 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X1) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq479 X3 (M.op (M.op X0 X1) X2) X0 (M.op X2 X1) X1
       have i₂ := eq53 X1 (M.op X0 X1) X2 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq53 eq479
    | exact resolve eq479 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq479
  have eq27473 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 (M.op x y)) X0)) = (M.op y (M.op x X0)) := by
    intro X0 X1
    first
    | exact superpose eq484 eq480
    | exact resolve eq480 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27474 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq486 eq480
    | exact resolve eq480 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq29033 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X2) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq243 eq559
    | exact resolve eq559 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29060 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op y (M.op x X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq241 eq559
    | exact resolve eq559 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq29062 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op (σ y) (M.op (σ x) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq244 eq559
    | exact resolve eq559 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq559
  have eq31370 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (M.op X0 (M.op X3 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq595 X2 X0 X2 X1 X3
       have i₂ := eq478 X1 X0 X2
       grind)
    | exact superpose eq478 eq595
    | exact resolve eq595 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34027 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X2) (M.op X3 (M.op (M.op X3 X4) X1))) = (M.op X4 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq595 x X4 X0 (M.op X3 (M.op (M.op X3 X4) X1)) X2
       have i₂ := eq601 X3 X4 X1 x X0
       grind)
    | exact superpose eq601 eq595
    | exact resolve eq595 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38791 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op X4 (M.op (M.op X1 (M.op X2 X4)) X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq477 X0 X1 X2 x X4 x
       have i₂ := eq474 X4 X1 X2 x x
       grind)
    | exact superpose eq474 eq477
    | exact resolve eq477 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq38934 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq38791
    | (have j0 := eq38791 X1 X0 (σ x) (σ y)
       grind)
    | exact resolve eq38791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39068 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op (M.op (M.op x y) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq484 eq38791
    | exact resolve eq38791 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq39069 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq486 eq38791
    | exact resolve eq38791 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39078 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq2127 eq38791
    | exact resolve eq38791 eq2127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq39089 : (M.op (M.op x y) y) = (M.op x (M.op y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq1534 eq38791
    | exact resolve eq38791 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq39092 : ∀ X0 X1 : G, (M.op X1 y) = (M.op x (M.op X0 (M.op (M.op X0 X1) (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq590 eq38791
    | exact resolve eq38791 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq39099 : (M.op (M.op x y) (σ y)) = (M.op (σ x) (M.op y (M.op x (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1536 eq38791
    | exact resolve eq38791 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq39100 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1733 eq38791
    | exact resolve eq38791 eq1733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39102 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (σ x) (M.op X0 (M.op (M.op X0 X1) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq591 eq38791
    | exact resolve eq38791 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq39399 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 (M.op (M.op (M.op (σ x) (σ y)) X3) (M.op X3 (σ y))))) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq486 (M.op (M.op X1 (M.op X2 (M.op (M.op sF4 X1) (M.op X1 sF3)))) X0) X1
       have i₂ := eq38791 X0 X1 X2 (M.op (M.op sF4 X1) (M.op X1 sF3))
       grind)
    | exact superpose eq38791 eq486
    | exact resolve eq486 eq38791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq38791
  have eq39460 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 (M.op (σ y) (M.op (σ x) (σ y))))) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1414 eq39399
    | exact resolve eq39399 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39399
  have eq49769 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op (M.op x y) (M.op X3 (M.op (M.op X3 (M.op x y)) X2)))) = (M.op X1 (M.op X0 (M.op (M.op X0 x) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15035 (M.op X0 (M.op (M.op X0 sF0) X2)) x
       have i₂ := eq565 X0 sF0 X2 x x x
       grind)
    | exact superpose eq565 eq15035
    | exact resolve eq15035 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15035
  have eq49777 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op (M.op X3 (M.op (σ x) (σ y))) X2)))) = (M.op X1 (M.op X0 (M.op (M.op X0 (σ x)) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15450 (M.op X0 (M.op (M.op X0 sF4) X2)) x
       have i₂ := eq565 X0 sF4 X2 sF2 x x
       grind)
    | exact superpose eq565 eq15450
    | exact resolve eq15450 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq15450
  have eq49954 : ∀ X1 X2 X3 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op (M.op X3 (M.op (σ x) (σ y))) X2)))) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X1 X2)))) := by
    intro X1 X2 X3
    first
    | exact superpose eq243 eq49777
    | exact resolve eq49777 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq49777
  have eq49957 : ∀ X1 X2 X3 : G, (M.op x (M.op (M.op x y) (M.op X3 (M.op (M.op X3 (M.op x y)) X2)))) = (M.op X1 (M.op (M.op x y) (M.op y (M.op X1 X2)))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq49769 x X1 X2 X3
       have i₂ := eq240 (M.op X1 X2) x
       grind)
    | exact superpose eq240 eq49769
    | exact resolve eq49769 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq49769
  have eq50456 : ∀ X1 X2 : G, (M.op (σ x) X2) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X1 X2)))) := by
    intro X1 X2
    first
    | (have i₁ := eq49954 X1 X2 x
       have i₂ := eq594 x sF4 X2
       grind)
    | exact superpose eq594 eq49954
    | exact resolve eq49954 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49954
  have eq50457 : ∀ X1 X2 : G, (M.op x X2) = (M.op X1 (M.op (M.op x y) (M.op y (M.op X1 X2)))) := by
    intro X1 X2
    first
    | (have i₁ := eq49957 X1 X2 x
       have i₂ := eq594 x sF0 X2
       grind)
    | exact superpose eq594 eq49957
    | exact resolve eq49957 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49957
  have eq244812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq120 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq244812
    | exact resolve eq244812 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244812
  have eq244824 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq244813
       have r₂ := eq28
       grind)
    | exact resolve eq244813 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244813
  have eq244828 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq244824
    | exact resolve eq244824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244824
  have eq244871 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq244828 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq244828
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq244828
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq244828
       grind)
    | exact resolve eq13 eq244828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244828
  have eq245100 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq244871
       have r₂ := eq27
       grind)
    | exact resolve eq244871 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244871
  have eq245145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq245100 eq120
    | exact resolve eq120 eq245100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq245100
  have eq245154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq245145
  have eq245157 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq245154
       have r₂ := eq28
       grind)
    | exact resolve eq245154 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245154
  have eq245413 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq245157 eq148
    | exact resolve eq148 eq245157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq245157
  have eq245796 : x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq29 eq245413
    | exact resolve eq245413 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245413
  have eq245797 : (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq245796
  have eq245911 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq245797
       grind)
    | exact superpose eq245797 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq245797
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq245797
       grind)
    | exact resolve eq13 eq245797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246059 : (M.op x x) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50457 y x
       have i₂ := eq245797
       grind)
    | exact superpose eq245797 eq50457
    | exact resolve eq50457 eq245797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50457 eq245797
  have eq246073 : (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq614 eq246059
    | exact resolve eq246059 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq246059
  have eq246140 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq245911
       have r₂ := eq19
       grind)
    | exact resolve eq245911 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245911
  have eq246182 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq246140
       grind)
    | exact superpose eq246140 eq103
    | exact resolve eq103 eq246140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq246140
  have eq246202 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq246182
    | exact resolve eq246182 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246182
  have eq247598 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq246073
       grind)
    | exact superpose eq246073 eq110
    | exact resolve eq110 eq246073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246073
  have eq247971 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq247598
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq247598
    | exact resolve eq247598 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247598
  have eq248390 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ x))))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq247971 eq9526
    | exact resolve eq9526 eq247971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9526 eq247971
  have eq248705 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1379 eq248390
    | exact resolve eq248390 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379 eq248390
  have eq248840 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq248705 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq248705
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq248705
       grind)
    | exact resolve eq13 eq248705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248705
  have eq249069 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq248840
       have r₂ := eq27
       grind)
    | exact resolve eq248840 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248840
  have eq249376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq249069 eq246202
    | exact resolve eq246202 eq249069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246202 eq249069
  have eq249378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq249376
  have eq249382 : x = (M.op y y) := by
    first
    | (have r₁ := eq249378
       have r₂ := eq28
       grind)
    | exact resolve eq249378 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249378
  have eq249385 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq249382
       grind)
    | exact superpose eq249382 eq110
    | exact resolve eq110 eq249382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249591 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq1262 y y X0
       have i₂ := eq249382
       grind)
    | exact superpose eq249382 eq1262
    | exact resolve eq1262 eq249382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249600 : y = (M.op (M.op (M.op x y) x) (M.op x x)) := by
    first
    | (have i₁ := eq1599 y y
       have i₂ := eq249382
       grind)
    | exact superpose eq249382 eq1599
    | exact resolve eq1599 eq249382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq249613 : x = (M.op x (M.op y (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq39092 y y
       have i₂ := eq249382
       grind)
    | exact superpose eq249382 eq39092
    | exact resolve eq39092 eq249382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39092
  have eq249614 : (M.op y (σ y)) = (M.op (σ x) (M.op y (M.op x (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq39102 y y
       have i₂ := eq249382
       grind)
    | exact superpose eq249382 eq39102
    | exact resolve eq39102 eq249382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249634 : (M.op (M.op x y) (σ y)) = (M.op y (σ y)) := by
    first
    | exact superpose eq39099 eq249614
    | exact resolve eq249614 eq39099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39099 eq249614
  have eq249635 : x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq39089 eq249613
    | exact resolve eq249613 eq39089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39089 eq249613
  have eq249642 : y = (M.op y (M.op x x)) := by
    first
    | exact superpose eq1265 eq249600
    | exact resolve eq249600 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265 eq249600
  have eq249648 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq249591 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq249591
    | (have j0 := eq249591 X0
       grind)
    | exact resolve eq249591 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq249591
  have eq249776 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq249385
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq249385
    | exact resolve eq249385 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249385
  have eq250735 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq249776 eq39102
    | exact resolve eq39102 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250755 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq39100 eq250735
    | exact resolve eq250735 eq39100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39100 eq250735
  have eq253679 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) := by
    first
    | exact superpose eq249648 eq141
    | exact resolve eq141 eq249648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq255076 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op X0 (M.op y x)) (M.op x x))) := by
    intro X0
    first
    | exact superpose eq249635 eq1160
    | exact resolve eq1160 eq249635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq255123 : (M.op x y) = (M.op (M.op (M.op x y) y) (M.op (M.op y (M.op x x)) (M.op x x))) := by
    first
    | exact superpose eq39068 eq255076
    | exact resolve eq255076 eq39068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255634 : y = (M.op (M.op (M.op (M.op (M.op x y) (M.op y x)) (M.op x x)) y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq7414 (M.op (M.op sF0 (M.op y x)) (M.op x x))
       have i₂ := eq255076 sF0
       grind)
    | exact superpose eq255076 eq7414
    | exact resolve eq7414 eq255076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7414 eq255076
  have eq255718 : y = (M.op (M.op (M.op (M.op (M.op x y) (M.op y x)) (M.op x x)) y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq249648 eq255634
    | exact resolve eq255634 eq249648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255634
  have eq256088 : (M.op x y) = (M.op (M.op (M.op x y) y) (M.op (M.op x (M.op x y)) (M.op x x))) := by
    first
    | (have i₁ := eq255123
       have i₂ := eq29060 x (M.op x x)
       grind)
    | exact superpose eq29060 eq255123
    | exact resolve eq255123 eq29060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29060 eq255123
  have eq256141 : y = (M.op (M.op (M.op (M.op x x) (M.op x x)) y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq2194 eq255718
    | exact resolve eq255718 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255718
  have eq256254 : (M.op x y) = (M.op x (M.op (M.op x (M.op x y)) (M.op x x))) := by
    first
    | exact superpose eq249635 eq256088
    | exact resolve eq256088 eq249635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256088
  have eq256271 : y = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq256141
       have i₂ := eq474 sF0 x x x y
       grind)
    | exact superpose eq474 eq256141
    | exact resolve eq256141 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq256141
  have eq256320 : (M.op x y) = (M.op y (M.op x (M.op x x))) := by
    first
    | exact superpose eq27473 eq256254
    | exact resolve eq256254 eq27473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27473 eq256254
  have eq256406 : (M.op (M.op (M.op x (M.op x y)) x) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq256271 eq246
    | exact resolve eq246 eq256271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq256641 : (M.op x x) = (M.op (M.op (M.op x (M.op x y)) x) (M.op x y)) := by
    first
    | (have i₁ := eq256406
       have i₂ := eq249382
       grind)
    | exact superpose eq249382 eq256406
    | exact resolve eq256406 eq249382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256406
  have eq256718 : (M.op x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq256641
       have i₂ := eq1262 sF0 x sF0
       grind)
    | exact superpose eq1262 eq256641
    | exact resolve eq256641 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256641
  have eq256761 : (M.op x x) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq249648 eq256718
    | exact resolve eq256718 eq249648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256718
  have eq261281 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X0 (M.op y (σ x))) (M.op x (M.op y (σ y))))) := by
    intro X0
    first
    | exact superpose eq249634 eq1199
    | exact resolve eq1199 eq249634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq249634
  have eq261842 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op x y) (M.op y (σ x))) (M.op x (M.op y (σ y)))) X0)) := by
    intro X0
    first
    | exact superpose eq261281 eq39068
    | exact resolve eq39068 eq261281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261281
  have eq261915 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) x) (M.op x (M.op y (σ y)))) X0)) := by
    intro X0
    first
    | exact superpose eq2194 eq261842
    | exact resolve eq261842 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194 eq261842
  have eq262226 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op y (σ y)))) X0)) := by
    intro X0
    first
    | exact superpose eq1411 eq261915
    | exact resolve eq261915 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261915
  have eq262308 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op y (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2516 eq262226
    | exact resolve eq262226 eq2516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262226
  have eq262329 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op y (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq3559 eq262308
    | exact resolve eq262308 eq3559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262308
  have eq262344 : ∀ X0 : G, (M.op x (M.op (M.op x y) X0)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq262329 X0
       have i₂ := eq239 X0 sF3
       grind)
    | exact superpose eq239 eq262329
    | exact resolve eq262329 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq262329
  have eq262349 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq249648 eq262344
    | exact resolve eq262344 eq249648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249648 eq262344
  have eq262859 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X0 (M.op (σ y) (σ x))) (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | exact superpose eq250755 eq1211
    | exact resolve eq1211 eq250755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq262918 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ x))) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq39069 eq262859
    | exact resolve eq262859 eq39069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39069
  have eq263023 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op (M.op X2 (M.op X1 (M.op (σ y) (σ x)))) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq262859 eq601
    | exact resolve eq601 eq262859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq263434 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq262859 eq4125
    | exact resolve eq4125 eq262859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4125
  have eq263460 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) (M.op (σ x) (σ x))) (σ y))) := by
    first
    | exact superpose eq262859 eq1414
    | exact resolve eq1414 eq262859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414 eq262859
  have eq263485 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ y))) := by
    first
    | exact superpose eq2516 eq263460
    | exact resolve eq263460 eq2516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2516 eq263460
  have eq263501 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ x))) = (M.op (M.op X0 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq263434 X0
       have i₂ := eq478 (M.op sF2 sF2) sF3 sF2
       grind)
    | exact superpose eq478 eq263434
    | exact resolve eq263434 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263434
  have eq263698 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq263023 x x X0
       have i₂ := eq595 X0 x (M.op sF3 sF2) x sF4
       grind)
    | exact superpose eq595 eq263023
    | exact resolve eq263023 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq263023
  have eq263765 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29062 eq262918
    | exact resolve eq262918 eq29062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262918
  have eq263825 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) (σ y))) := by
    first
    | exact superpose eq1411 eq263485
    | exact resolve eq263485 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263485
  have eq263835 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq7473 eq263501
    | exact resolve eq263501 eq7473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263501
  have eq263887 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq3228 eq263698
    | exact resolve eq263698 eq3228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228 eq263698
  have eq263900 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq250755 eq263765
    | exact resolve eq263765 eq250755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263765
  have eq263917 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq251 eq263825
    | exact resolve eq263825 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263825
  have eq263932 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq249776 eq263887
    | exact resolve eq263887 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263887
  have eq263937 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq27474 eq263900
    | exact resolve eq263900 eq27474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27474 eq263900
  have eq263942 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1625 eq263917
    | exact resolve eq263917 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263917
  have eq263950 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq249776 eq263942
    | exact resolve eq263942 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263942
  have eq264004 : (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq263835 eq251
    | exact resolve eq251 eq263835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264129 : (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq263835 eq1625
    | exact resolve eq1625 eq263835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264135 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ y) (σ y))) (σ y)) := by
    first
    | exact superpose eq263835 eq24094
    | exact resolve eq24094 eq263835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24094
  have eq264159 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ y) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq264135
       have i₂ := eq1262 sF2 sF2 (M.op sF3 sF3)
       grind)
    | exact superpose eq1262 eq264135
    | exact resolve eq264135 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264135
  have eq264163 : (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq39078 eq264129
    | exact resolve eq264129 eq39078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39078 eq264129
  have eq264220 : (M.op (σ y) (σ x)) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq249776 eq264004
    | exact resolve eq264004 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264004
  have eq264255 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq249776 eq264159
    | exact resolve eq264159 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264159
  have eq264257 : (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq254 eq264163
    | exact resolve eq264163 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq264163
  have eq264280 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq264220
       have i₂ := eq1262 sF2 sF2 sF4
       grind)
    | exact superpose eq1262 eq264220
    | exact resolve eq264220 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264220
  have eq264298 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq250755 eq264257
    | exact resolve eq264257 eq250755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264257
  have eq264339 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq263950 eq641
    | exact resolve eq641 eq263950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264345 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq263950 eq1733
    | exact resolve eq1733 eq263950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733
  have eq264641 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq264345
       have i₂ := eq478 (M.op sF2 sF4) sF2 sF2
       grind)
    | exact superpose eq478 eq264345
    | exact resolve eq264345 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264345
  have eq276049 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) X0) := by
    intro X0
    first
    | exact superpose eq250755 eq1247
    | exact resolve eq1247 eq250755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq276050 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq264339 eq276049
    | exact resolve eq276049 eq264339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264339 eq276049
  have eq276051 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq264280 eq276050
    | exact resolve eq276050 eq264280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276050
  have eq276163 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq276051 eq38934
    | exact resolve eq38934 eq276051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38934
  have eq276777 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) X0) = (M.op (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq276051 eq1245
    | exact resolve eq1245 eq276051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276792 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq264641 eq276777
    | exact resolve eq276777 eq264641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264641 eq276777
  have eq277367 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq276792 x
       have i₂ := eq1262 sF4 sF3 x
       grind)
    | exact superpose eq1262 eq276792
    | exact resolve eq276792 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276792
  have eq314428 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq256761 eq253679
    | exact resolve eq253679 eq256761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253679
  have eq314429 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq314428
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq314428
    | exact resolve eq314428 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq314428
  have eq314449 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq314429 eq263835
    | exact resolve eq263835 eq314429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263835
  have eq315040 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) := by
    first
    | exact superpose eq314449 eq588
    | exact resolve eq588 eq314449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314449
  have eq317462 : (σ y) = (M.op (σ (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq315040 eq7473
    | exact resolve eq7473 eq315040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7473
  have eq317765 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)))) := by
    first
    | exact superpose eq8509 eq317462
    | exact resolve eq317462 eq8509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8509 eq317462
  have eq317855 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq315040 eq317765
    | exact resolve eq317765 eq315040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315040 eq317765
  have eq330345 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq314429 eq263932
    | exact resolve eq263932 eq314429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263932
  have eq330346 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq314429 eq263937
    | exact resolve eq263937 eq314429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263937
  have eq331663 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ y) (M.op (σ x) (σ y))))) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq3559 eq2384
    | exact resolve eq2384 eq3559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384 eq3559
  have eq331664 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | exact superpose eq263950 eq331663
    | exact resolve eq331663 eq263950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331663
  have eq331665 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq314429 eq331664
    | exact resolve eq331664 eq314429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331664
  have eq331769 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1)) = (M.op (M.op (M.op (σ y) X0) (σ y)) (M.op (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq331665 eq1411
    | exact resolve eq1411 eq331665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq332014 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ y) X0) (σ y)) (M.op (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ y))) := by
    intro X0
    first
    | exact superpose eq331665 eq1388
    | exact resolve eq1388 eq331665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388 eq331665
  have eq332082 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq332014 X0
       have i₂ := eq1262 X0 sF3 (M.op (M.op X0 (M.op sF1 sF1)) sF3)
       grind)
    | exact superpose eq1262 eq332014
    | exact resolve eq332014 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332014
  have eq332298 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1)) = (M.op X0 (M.op (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq331769 X0 X1
       have i₂ := eq1262 X0 sF3 (M.op (M.op X0 (M.op sF1 sF1)) X1)
       grind)
    | exact superpose eq1262 eq331769
    | exact resolve eq331769 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331769
  have eq332409 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq251 eq332082
    | exact resolve eq332082 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq332082
  have eq332576 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X1)) := by
    intro X1
    first
    | (have i₁ := eq332298 X1 x
       have i₂ := eq1445 x X1 sF1 sF1
       grind)
    | exact superpose eq1445 eq332298
    | exact resolve eq332298 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332298
  have eq332641 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq1625 eq332409
    | exact resolve eq332409 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332409
  have eq332729 : ∀ X1 : G, (M.op (σ y) (M.op (σ y) X1)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X1)) := by
    intro X1
    first
    | exact superpose eq277367 eq332576
    | exact resolve eq332576 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332576
  have eq332752 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq3215 eq332641
    | exact resolve eq332641 eq3215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3215 eq332641
  have eq332812 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq277367 eq332752
    | exact resolve eq332752 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332752
  have eq332845 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq249776 eq332812
    | exact resolve eq332812 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332812
  have eq332859 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq264280 eq332845
    | exact resolve eq332845 eq264280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264280 eq332845
  have eq334712 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq29062 eq2401
    | exact resolve eq2401 eq29062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq334713 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq277367 eq334712
    | exact resolve eq334712 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334712
  have eq334835 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) X1) = (M.op (M.op (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq334713 eq29062
    | exact resolve eq29062 eq334713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335209 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq334835 X1 x
       have i₂ := eq1452 sF4 X1 sF3 x
       grind)
    | exact superpose eq1452 eq334835
    | exact resolve eq334835 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq334835
  have eq335391 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq335209 X0 X0
       have i₂ := eq478 X0 (M.op X0 sF4) sF3
       grind)
    | exact superpose eq478 eq335209
    | exact resolve eq335209 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq335209
  have eq349075 : (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (M.op (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ y)) := by
    first
    | exact superpose eq330346 eq39102
    | exact resolve eq39102 eq330346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39102
  have eq349096 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ y)) := by
    first
    | exact superpose eq334713 eq349075
    | exact resolve eq349075 eq334713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334713 eq349075
  have eq349268 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ y)) := by
    first
    | exact superpose eq264298 eq349096
    | exact resolve eq349096 eq264298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264298 eq349096
  have eq349387 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ y)) := by
    first
    | exact superpose eq264255 eq349268
    | exact resolve eq349268 eq264255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264255 eq349268
  have eq351970 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ (M.op x y)) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq332859 eq14
    | exact resolve eq14 eq332859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332859
  have eq352282 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ y) (M.op (M.op (σ (M.op x y)) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq276051 eq351970
    | exact resolve eq351970 eq276051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276051 eq351970
  have eq380412 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X0) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq277367 eq14908
    | exact resolve eq14908 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14908
  have eq380547 : ∀ X0 : G, (M.op (M.op (σ y) (M.op X0 (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ y) X0) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq380412 eq380412
    | exact resolve eq380412 eq380412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380412
  have eq381430 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op X0 (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq249776 eq380547
    | exact resolve eq380547 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380547
  have eq381795 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq2603 eq381430
    | exact resolve eq381430 eq2603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603 eq381430
  have eq381986 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq1625 eq381795
    | exact resolve eq381795 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625 eq381795
  have eq382068 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq249776 eq381986
    | exact resolve eq381986 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381986
  have eq390545 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (M.op (σ y) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) = (k (σ y) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq349387 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))
       grind)
    | exact resolve eq13 eq349387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349387
  have eq390913 : (M.op (σ y) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) = (k (σ y) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have r₁ := eq390545
       have r₂ := eq330346
       grind)
    | exact resolve eq390545 eq330346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390545
  have eq391070 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq330346 eq390913
    | exact resolve eq390913 eq330346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330346 eq390913
  have eq495609 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) X1)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X1)) := by
    intro X1
    first
    | exact superpose eq276163 eq332729
    | exact resolve eq332729 eq276163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332729
  have eq505519 : (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq330345 eq513
    | exact resolve eq513 eq330345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq505520 : (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq39068 eq505519
    | exact resolve eq505519 eq39068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39068 eq505519
  have eq505521 : (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op x (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq505520
       have i₂ := eq262349 sF0
       grind)
    | exact superpose eq262349 eq505520
    | exact resolve eq505520 eq262349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262349 eq505520
  have eq505522 : (σ (M.op x (M.op x x))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq256761 eq505521
    | exact resolve eq505521 eq256761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505521
  have eq506248 : (k (σ y) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) = (σ (k y (M.op x (M.op x x)))) := by
    first
    | (have i₁ := eq37 (M.op x (M.op x x))
       have i₂ := eq505522
       grind)
    | exact superpose eq505522 eq37
    | exact resolve eq37 eq505522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq505522
  have eq506370 : (M.op (σ x) (σ y)) = (σ (k y (M.op x (M.op x x)))) := by
    first
    | exact superpose eq391070 eq506248
    | exact resolve eq506248 eq391070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391070 eq506248
  have eq530855 : ∀ X0 X2 : G, (M.op (M.op (σ x) X0) (M.op (σ y) X2)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq658 X0 x x
       have i₂ := eq1279 X0 x sF4 x
       grind)
    | exact superpose eq1279 eq658
    | exact resolve eq658 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq1279
  have eq530856 : ∀ X0 X2 : G, (M.op (M.op (σ x) X0) (M.op (σ y) X2)) = (M.op (σ y) (M.op X0 X2)) := by
    intro X0 X2
    first
    | exact superpose eq277367 eq530855
    | exact resolve eq530855 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530855
  have eq534421 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y))) := by
    intro X0
    first
    | exact superpose eq660 eq654
    | exact resolve eq654 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq660
  have eq534518 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) X0)) (σ y))) := by
    intro X0
    first
    | exact superpose eq277367 eq534421
    | exact resolve eq534421 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534421
  have eq535969 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq29062 eq534518
    | exact resolve eq534518 eq29062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29062 eq534518
  have eq536935 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq335391 eq535969
    | exact resolve eq535969 eq335391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535969
  have eq537452 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq536935
    | (have j0 := eq536935 X0
       grind)
    | exact resolve eq536935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536935
  have eq537692 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq277367 eq537452
    | exact resolve eq537452 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537452
  have eq637364 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (σ x)) X0) = (M.op X1 (M.op X2 (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq277367 eq2536
    | exact resolve eq2536 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2536
  have eq637365 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (σ x)) X0) = (M.op X1 (M.op X2 (M.op (σ x) (M.op (σ x) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq276163 eq637364
    | exact resolve eq637364 eq276163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637364
  have eq637366 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (σ x)) X0) = (M.op X1 (M.op X2 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq495609 eq637365
    | exact resolve eq637365 eq495609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637365
  have eq639769 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) X0)) = (M.op (σ (M.op x y)) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq637366 eq50456
    | exact resolve eq50456 eq637366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50456
  have eq639822 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) X0)) = (M.op (σ (M.op x y)) (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq639769 x
       have i₂ := eq26211 sF3 sF4 sF2 x
       grind)
    | (have i₁ := eq639769 x
       have i₂ := eq26211 sF2 sF4 sF3 x
       grind)
    | exact superpose eq26211 eq639769
    | exact resolve eq639769 eq26211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26211 eq639769
  have eq641071 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1245 eq639822
    | exact resolve eq639822 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245 eq639822
  have eq641985 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq314429 eq641071
    | exact resolve eq641071 eq314429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641071
  have eq642608 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq330345 eq641985
    | exact resolve eq641985 eq330345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330345 eq641985
  have eq705023 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op X1 (σ y)) X2)) = (M.op X1 (M.op (M.op (σ x) (σ y)) X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq4106 X1 x x
       have i₂ := eq1445 x X1 sF4 x
       grind)
    | exact superpose eq1445 eq4106
    | exact resolve eq4106 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445 eq4106
  have eq705024 : ∀ X1 X2 : G, (M.op X1 (M.op (σ y) X2)) = (M.op (σ x) (M.op (M.op X1 (σ y)) X2)) := by
    intro X1 X2
    first
    | exact superpose eq277367 eq705023
    | exact resolve eq705023 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705023
  have eq705194 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op X0 (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq9827 eq705024
    | exact resolve eq705024 eq9827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9827 eq705024
  have eq706173 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) X0) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq249776 eq705194
    | exact resolve eq705194 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705194
  have eq706593 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq530856 eq706173
    | exact resolve eq706173 eq530856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706173
  have eq803533 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = (M.op (σ x) (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) X1) X0))) := by
    intro X0 X1
    first
    | exact superpose eq277367 eq15767
    | exact resolve eq15767 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15767
  have eq803534 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) X1) X0))) := by
    intro X0 X1
    first
    | exact superpose eq277367 eq803533
    | exact resolve eq803533 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803533
  have eq803535 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (M.op (σ y) X0))) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) X1) X0))) := by
    intro X0 X1
    first
    | exact superpose eq277367 eq803534
    | exact resolve eq803534 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803534
  have eq803536 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (M.op (σ x) X0))) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) X1) X0))) := by
    intro X0 X1
    first
    | exact superpose eq276163 eq803535
    | exact resolve eq803535 eq276163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803535
  have eq803537 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0))) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) X1) X0))) := by
    intro X0 X1
    first
    | exact superpose eq495609 eq803536
    | exact resolve eq803536 eq495609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803536
  have eq825417 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op X1 (M.op (M.op X1 X0) (M.op (σ x) (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq250755 eq18354
    | exact resolve eq18354 eq250755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18354 eq250755
  have eq825418 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op X1 (M.op (M.op X1 X0) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq314429 eq825417
    | exact resolve eq825417 eq314429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825417
  have eq826377 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op (M.op X0 (σ y)) (σ y))) = (M.op (M.op (M.op X1 X0) X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq825418 eq31370
    | exact resolve eq31370 eq825418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31370
  have eq826876 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y)))) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq825418 eq352282
    | exact resolve eq352282 eq825418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352282
  have eq827038 : ∀ X0 : G, (M.op (σ x) (M.op (M.op X0 (σ y)) (σ y))) = (M.op X0 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq825418 eq803537
    | exact resolve eq803537 eq825418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803537 eq825418
  have eq827168 : ∀ X0 : G, (M.op (σ x) (M.op (M.op X0 (σ y)) (σ y))) = (M.op (M.op (M.op (σ (M.op x y)) X0) (σ x)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq637366 eq827038
    | exact resolve eq827038 eq637366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637366 eq827038
  have eq827307 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ (M.op x y)))) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq826876 x
       have i₂ := eq9821 sF1 sF3 x sF1
       grind)
    | exact superpose eq9821 eq826876
    | exact resolve eq826876 eq9821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9821 eq826876
  have eq827736 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq826377 X0 x
       have i₂ := eq1262 X0 x sF1
       grind)
    | exact superpose eq1262 eq826377
    | exact resolve eq826377 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262 eq826377
  have eq828647 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (σ x)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq382068 eq827168
    | exact resolve eq827168 eq382068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382068 eq827168
  have eq828751 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ (M.op x y)))) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq537692 eq827307
    | exact resolve eq827307 eq537692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537692 eq827307
  have eq832413 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) X0) (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq828647 eq594
    | exact resolve eq594 eq828647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq828647
  have eq908402 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X2) = (M.op (σ y) (M.op (σ y) (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq277367 eq29033
    | exact resolve eq29033 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29033
  have eq908403 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X2) = (M.op (σ x) (M.op (σ x) (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq276163 eq908402
    | exact resolve eq908402 eq276163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276163 eq908402
  have eq908404 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X2) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq495609 eq908403
    | exact resolve eq908403 eq495609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495609 eq908403
  have eq909801 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) := by
    intro X0
    first
    | exact superpose eq641 eq908404
    | exact resolve eq908404 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq908404
  have eq910717 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op X0 (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq335391 eq909801
    | exact resolve eq909801 eq335391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335391 eq909801
  have eq912061 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq827736 eq910717
    | exact resolve eq910717 eq827736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827736 eq910717
  have eq913022 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq530856 eq912061
    | exact resolve eq912061 eq530856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530856 eq912061
  have eq913617 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq706593 eq913022
    | exact resolve eq913022 eq706593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706593 eq913022
  have eq960217 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq828751 eq588
    | exact resolve eq588 eq828751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828751
  have eq988262 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ x)))) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq263950 eq39460
    | exact resolve eq39460 eq263950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39460 eq263950
  have eq988263 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 (M.op (σ (M.op x y)) (σ (M.op x y))))) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq314429 eq988262
    | exact resolve eq988262 eq314429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314429 eq988262
  have eq989805 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) = (M.op (σ x) (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq988263 X1 (M.op X1 sF1) x
       have i₂ := eq14 sF1 X1 sF1
       grind)
    | exact superpose eq14 eq988263
    | exact resolve eq988263 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988263
  have eq991469 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 (σ (M.op x y))) X1)) = (M.op (σ (M.op x y)) (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq642608 eq989805
    | exact resolve eq989805 eq642608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642608 eq989805
  have eq2413364 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq249635 eq121
    | exact resolve eq121 eq249635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2413365 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2413364
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2413364
    | exact resolve eq2413364 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413364
  have eq2413366 : x = (M.op x y) ∨ (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2413365
       have i₂ := eq249382
       grind)
    | exact superpose eq249382 eq2413365
    | exact resolve eq2413365 eq249382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249382 eq2413365
  have eq2413367 : (M.op x x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq256761 eq2413366
    | exact resolve eq2413366 eq256761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256761 eq2413366
  have eq2413368 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq249635 eq2413367
    | exact resolve eq2413367 eq249635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249635 eq2413367
  have eq2924812 : ∀ X1 X2 X3 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 X1) X2))) = (M.op X1 (M.op X3 (M.op (σ y) X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq8073 X3 x X1 X2
       have i₂ := eq34027 sF3 X1 X2 X3 x
       grind)
    | exact superpose eq34027 eq8073
    | exact resolve eq8073 eq34027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8073 eq34027
  have eq2924813 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X3 (M.op (σ y) X2))) = (M.op (σ x) (M.op (σ y) (M.op (M.op X3 X1) X2))) := by
    intro X1 X2 X3
    first
    | exact superpose eq277367 eq2924812
    | exact resolve eq2924812 eq277367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277367 eq2924812
  have eq3724341 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ (M.op x y))) (k (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    intro X0
    first
    | exact superpose eq105 eq22123
    | (have j0 := eq22123 y (M.op x y) x
       grind)
    | exact resolve eq22123 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq22123
  have eq3726868 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ (M.op x y))) (k (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    intro X0
    first
    | exact superpose eq21 eq3724341
    | (have j0 := eq3724341 X0
       grind)
    | exact resolve eq3724341 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724341
  have eq3728028 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (k (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq991469 eq3726868
    | exact resolve eq3726868 eq991469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991469 eq3726868
  have eq3728780 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (k (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3728028
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3728028
    | exact resolve eq3728028 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728028
  have eq3729352 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (k (σ y) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq3728780
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq3728780
    | exact resolve eq3728780 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728780
  have eq3729772 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (k (σ y) (σ (M.op x y))))) := by
    first
    | exact superpose eq249776 eq3729352
    | exact resolve eq3729352 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729352
  have eq3730066 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (k (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq3729772
    | exact resolve eq3729772 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729772
  have eq3730590 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (k (σ y) (σ (M.op x y)))) (σ x)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3730066 eq832413
    | exact resolve eq832413 eq3730066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832413 eq3730066
  have eq3731337 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2924813 eq3730590
    | exact resolve eq3730590 eq2924813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924813 eq3730590
  have eq3731595 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (M.op (σ (M.op x y)) (M.op (σ y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq913617 eq3731337
    | exact resolve eq3731337 eq913617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913617 eq3731337
  have eq3731762 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq317855 eq3731595
    | exact resolve eq3731595 eq317855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317855 eq3731595
  have eq3732020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2413368 eq3731762
    | exact resolve eq3731762 eq2413368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413368 eq3731762
  have eq3732745 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq3732020
    | exact resolve eq3732020 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3732020
  have eq3732914 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3732745
       have r₂ := eq28
       grind)
    | exact resolve eq3732745 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732745
  have eq3733121 : (M.op x y) = (M.op y (M.op x x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq256320
       have i₂ := eq3732914
       grind)
    | exact superpose eq3732914 eq256320
    | exact resolve eq256320 eq3732914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256320 eq3732914
  have eq3734058 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3733121
       have i₂ := eq249642
       grind)
    | exact superpose eq249642 eq3733121
    | exact resolve eq3733121 eq249642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249642 eq3733121
  have eq3741800 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3734058 eq29
    | exact resolve eq29 eq3734058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3734058
  have eq3742679 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq3741800
    | exact resolve eq3741800 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3741800
  have eq3742680 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3742679
  have eq3743243 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3742680 eq21
    | exact resolve eq21 eq3742680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3742680
  have eq3743873 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3743243
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3743243
    | exact resolve eq3743243 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3743243
  have eq3749239 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3743873 eq960217
    | exact resolve eq960217 eq3743873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960217 eq3743873
  have eq3749415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3749239 x
       have i₂ := eq588 sF4 x sF1
       grind)
    | exact superpose eq588 eq3749239
    | exact resolve eq3749239 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq3749239
  have eq3749760 : x = (M.op x y) := by
    first
    | (have r₁ := eq3749415
       have r₂ := eq28
       grind)
    | exact resolve eq3749415 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3749415
  have eq3756017 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3749760 eq21
    | exact resolve eq21 eq3749760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3756275 : y = (M.op x (M.op x x)) := by
    first
    | exact superpose eq3749760 eq256271
    | exact resolve eq256271 eq3749760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256271 eq3749760
  have eq3756655 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3756017
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3756017
    | exact resolve eq3756017 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3756017
  have eq3765670 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq506370
       have i₂ := eq3756275
       grind)
    | exact superpose eq3756275 eq506370
    | exact resolve eq506370 eq3756275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506370 eq3756275
  have eq3766617 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3765670
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq3765670
    | exact resolve eq3765670 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq3765670
  have eq3766982 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3766617
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq3766617
    | exact resolve eq3766617 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq3766617
  have eq3767241 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq249776 eq3766982
    | exact resolve eq3766982 eq249776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249776 eq3766982
  have eq3767424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3756655 eq3767241
    | exact resolve eq3767241 eq3756655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756655 eq3767241
  have eq3767535 : False := by grind
  exact eq3767535

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pyx_Equation947 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
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
  clear eq35
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
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq97 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq111 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq104
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq879 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
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
  have eq1142 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq1147 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq1161 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
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
  have eq1167 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1147 X0 X1
       have i₂ := eq652 X1 X0 X0
       grind)
    | exact superpose eq652 eq1147
    | exact resolve eq1147 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1201 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
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
  have eq1205 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | exact superpose eq1057 eq1079
    | exact resolve eq1079 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1293 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq1060
    | (have j0 := eq1060 (σ x)
       grind)
    | exact resolve eq1060 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1297 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq1060 eq1079
    | exact resolve eq1079 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1558 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq213 eq1142
    | exact resolve eq1142 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1560 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y y) (M.op (M.op y y) (M.op y y)))) := by
    first
    | (have i₁ := eq1142 (M.op y y) x
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq1142
    | exact resolve eq1142 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq222 eq1142
    | exact resolve eq1142 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1566 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1293 eq1142
    | exact resolve eq1142 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1592 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq1566
       have i₂ := eq1079 (M.op sF3 sF3) sF3
       grind)
    | exact superpose eq1079 eq1566
    | exact resolve eq1566 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1594 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1564
       have i₂ := eq1079 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq1079 eq1564
    | exact resolve eq1564 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1597 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq1560
       have i₂ := eq1079 (M.op y y) y
       grind)
    | exact superpose eq1079 eq1560
    | exact resolve eq1560 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq1599 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1558
       have i₂ := eq1079 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq1079 eq1558
    | exact resolve eq1558 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558
  have eq1627 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1594 eq222
    | exact resolve eq222 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq1649 : y = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq1599 eq213
    | exact resolve eq213 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1654 : (M.op x y) ≠ (M.op y (M.op x y)) ∨ (M.op y (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1599 eq13
    | exact resolve eq13 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1750 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq1594 eq1592
    | exact resolve eq1592 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq1796 : (M.op y y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq1599 eq1597
    | exact resolve eq1597 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597
  have eq2260 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1167 (M.op X1 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq1142 X0 X1
       grind)
    | exact superpose eq1142 eq1167
    | exact resolve eq1167 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq2268 : (M.op (M.op y (M.op y y)) y) = (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1205 eq1167
    | exact resolve eq1167 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq2276 : (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1297 eq1167
    | exact resolve eq1167 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq2280 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1079 X1 X0
       have i₂ := eq1167 X1 X0
       grind)
    | (have i₁ := eq1079 X1 X1
       have i₂ := eq1167 X1 X1
       grind)
    | exact superpose eq1167 eq1079
    | exact resolve eq1079 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2349 : (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) := by
    first
    | (have i₁ := eq2276
       have i₂ := eq652 (M.op sF3 sF3) sF3 sF3
       grind)
    | exact superpose eq652 eq2276
    | exact resolve eq2276 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276
  have eq2357 : (M.op (M.op y (M.op y y)) y) = (M.op (M.op x y) (M.op y (M.op (M.op y y) (M.op y y)))) := by
    first
    | (have i₁ := eq2268
       have i₂ := eq652 (M.op y y) y y
       grind)
    | exact superpose eq652 eq2268
    | exact resolve eq2268 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268
  have eq2364 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2260 X0 X1
       have i₂ := eq652 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq652 eq2260
    | exact resolve eq2260 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq2260
  have eq2392 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq2349
       have i₂ := eq14 sF3 sF3 sF3
       grind)
    | exact superpose eq14 eq2349
    | exact resolve eq2349 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349
  have eq2398 : (M.op (M.op x y) y) = (M.op (M.op y (M.op y y)) y) := by
    first
    | (have i₁ := eq2357
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq2357
    | exact resolve eq2357 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357
  have eq2403 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2364 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2364
    | exact resolve eq2364 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2364
  have eq2418 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq2392
       have i₂ := eq1161 sF3 sF3
       grind)
    | exact superpose eq1161 eq2392
    | exact resolve eq2392 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392
  have eq2424 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2398
       have i₂ := eq1161 y y
       grind)
    | exact superpose eq1161 eq2398
    | exact resolve eq2398 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq2429 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2403 X0 X1
       have i₂ := eq1161 X0 X0
       grind)
    | exact superpose eq1161 eq2403
    | exact resolve eq2403 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161 eq2403
  have eq6113 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq97 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq97
    | (have j0 := eq97 y
       grind)
    | exact resolve eq97 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq6139 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6113
  have eq6145 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6139
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq6139
    | exact resolve eq6139 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq6139
  have eq6168 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6145
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6145 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6145
  have eq6189 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6168 eq89
    | exact resolve eq89 eq6168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq6983 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq7000 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6983 X0
       have j1 := eq13 (σ X0) (σ y)
       grind)
    | (have r₁ := eq6983 X0
       have r₂ := eq13 (σ y) (σ X0)
       grind)
    | (have r₁ := eq6983 X0
       have r₂ := eq13 (σ X0) (σ y)
       grind)
    | exact resolve eq6983 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6983
  have eq7031 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq7000
    | (have j0 := eq7000 X0
       grind)
    | exact resolve eq7000 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq7000
  have eq18099 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6168 eq111
    | exact resolve eq111 eq6168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq6168
  have eq18117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18117
    | exact resolve eq18117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18117
  have eq18129 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq18118
       have r₂ := eq27
       grind)
    | exact resolve eq18118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18118
  have eq18131 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18129
    | exact resolve eq18129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18129
  have eq18133 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18131 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18131
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18131
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18131
       grind)
    | exact resolve eq12 eq18131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18134 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18131 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18131
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18131
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18131
       grind)
    | exact resolve eq13 eq18131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18145 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18131 eq2280
    | exact resolve eq2280 eq18131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18131
  have eq18147 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq18134
  have eq18148 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq18133
  have eq18149 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18145
       have i₂ := eq1167 sF2 sF3
       grind)
    | exact superpose eq1167 eq18145
    | exact resolve eq18145 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18145
  have eq18152 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18147
    | exact resolve eq18147 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18147
  have eq18153 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18148
    | exact resolve eq18148 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18148
  have eq18154 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq18153
  have eq18155 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1293 eq18149
    | exact resolve eq18149 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18149
  have eq18156 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1594 eq18155
    | exact resolve eq18155 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18155
  have eq18162 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18152 eq59
    | exact resolve eq59 eq18152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq18152
  have eq18179 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18154 eq84
    | exact resolve eq84 eq18154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq18180 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18154 eq117
    | exact resolve eq117 eq18154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq18154
  have eq18194 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18180
  have eq18203 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq18179
    | exact resolve eq18179 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18179
  have eq18286 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18194
       grind)
    | exact superpose eq18194 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18194
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18194
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18194
       grind)
    | exact resolve eq12 eq18194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18287 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18194
       grind)
    | exact superpose eq18194 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18194
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18194
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18194
       grind)
    | exact resolve eq13 eq18194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18194
  have eq18300 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18287
  have eq18301 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18286
  have eq18305 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18300
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18300
    | exact resolve eq18300 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18300
  have eq18306 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18301
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18301
    | exact resolve eq18301 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18301
  have eq18307 : y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18306
  have eq18311 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq18305
       grind)
    | exact superpose eq18305 eq44
    | exact resolve eq44 eq18305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq18305
  have eq18335 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18311
    | exact resolve eq18311 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18311
  have eq18359 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18307
       grind)
    | exact superpose eq18307 eq74
    | exact resolve eq74 eq18307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq18307
  have eq18383 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18359
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18359
    | exact resolve eq18359 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18359
  have eq18652 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18383 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq18383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18383
  have eq18656 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18652
    | exact resolve eq18652 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18652
  have eq18668 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18656
    | exact resolve eq18656 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18656
  have eq18669 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18668
  have eq21384 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18156 eq1750
    | exact resolve eq1750 eq18156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750 eq18156
  have eq21427 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq21384
    | exact resolve eq21384 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21384
  have eq21439 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18203
       grind)
    | exact superpose eq18203 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18203
  have eq21447 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21439
  have eq21454 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21447
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21447
    | exact resolve eq21447 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21447
  have eq21468 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21454
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21454
    | exact resolve eq21454 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21454
  have eq21469 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21468
  have eq21493 : y ≠ y ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq21469
       grind)
    | exact superpose eq21469 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21469
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21469
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21469
       grind)
    | exact resolve eq13 eq21469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21504 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2280 x y
       have i₂ := eq21469
       grind)
    | exact superpose eq21469 eq2280
    | exact resolve eq2280 eq21469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21469
  have eq21506 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21493
  have eq21508 : x = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21504
       have i₂ := eq1167 x y
       grind)
    | exact superpose eq1167 eq21504
    | exact resolve eq21504 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21504
  have eq21511 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21506
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21506
    | exact resolve eq21506 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21506
  have eq21514 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21508
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq21508
    | exact resolve eq21508 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21508
  have eq21515 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1599 eq21514
    | exact resolve eq21514 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21514
  have eq22495 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq900 x y
       have i₂ := eq21511
       grind)
    | exact superpose eq21511 eq900
    | (have j0 := eq900 x y
       grind)
    | exact resolve eq900 eq21511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21511
  have eq22498 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22495
    | exact resolve eq22495 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22495
  have eq22512 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22498
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22498
    | exact resolve eq22498 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22498
  have eq22521 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22512
    | exact resolve eq22512 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22512
  have eq22528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22521
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22521
    | exact resolve eq22521 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22521
  have eq22535 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22528
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22528
    | exact resolve eq22528 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22528
  have eq22546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22535
    | exact resolve eq22535 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22535
  have eq22554 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22546
       have r₂ := eq27
       grind)
    | exact resolve eq22546 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22546
  have eq22562 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22554
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22554
    | exact resolve eq22554 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22554
  have eq22564 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22562
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22562
    | exact resolve eq22562 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22562
  have eq22565 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22564
    | exact resolve eq22564 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22564
  have eq22566 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq22565
  have eq23625 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21515 eq1796
    | exact resolve eq1796 eq21515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796 eq21515
  have eq23668 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23625
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23625
    | exact resolve eq23625 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23625
  have eq26736 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21427 eq6189
    | exact resolve eq6189 eq21427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21427
  have eq36418 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18162
       grind)
    | exact superpose eq18162 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18162
  have eq36428 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq36418
  have eq36447 : x = (M.op x y) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36428
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36428
    | exact resolve eq36428 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36428
  have eq36448 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq36447
  have eq36558 : y ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq36448
  have eq37013 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18669 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18669
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18669
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18669
       grind)
    | exact resolve eq13 eq18669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18669
  have eq37027 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq37013
  have eq37032 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq37027
    | exact resolve eq37027 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37027
  have eq37600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37032 eq18335
    | exact resolve eq18335 eq37032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18335 eq37032
  have eq37613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq37600
  have eq37618 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq37613
       have r₂ := eq27
       grind)
    | exact resolve eq37613 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37613
  have eq37633 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37618 eq1627
    | exact resolve eq1627 eq37618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37665 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq37678 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1293 eq37633
    | exact resolve eq37633 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293 eq37633
  have eq37684 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1594 eq37678
    | exact resolve eq37678 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594 eq37678
  have eq37775 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37618 eq37684
    | exact resolve eq37684 eq37618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37618 eq37684
  have eq37822 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq37775
  have eq37845 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq37822
       have r₂ := eq37665
       grind)
    | exact resolve eq37822 eq37665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37665 eq37822
  have eq38401 : (τ (σ y)) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37845 eq6189
    | exact resolve eq6189 eq37845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37845
  have eq38491 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq38401
    | exact resolve eq38401 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq38401
  have eq39137 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq38491
       grind)
    | exact superpose eq38491 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq38491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38491
  have eq39156 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq39137
  have eq40086 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23668
       have i₂ := eq39156
       grind)
    | exact superpose eq39156 eq23668
    | exact resolve eq23668 eq39156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23668 eq39156
  have eq40156 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq40086
  have eq40178 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq40156
       have r₂ := eq22566
       grind)
    | exact resolve eq40156 eq22566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22566 eq40156
  have eq40216 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40178 eq1627
    | exact resolve eq1627 eq40178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627 eq40178
  have eq40726 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40216 eq2280
    | exact resolve eq2280 eq40216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40216
  have eq40775 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40726 eq6189
    | exact resolve eq6189 eq40726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40726
  have eq40865 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq40775
    | exact resolve eq40775 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq40775
  have eq41511 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq40865
       grind)
    | exact superpose eq40865 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq40865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41528 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq41511
  have eq363284 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq41528
       grind)
    | exact superpose eq41528 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq41528
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq41528
       grind)
    | exact resolve eq13 eq41528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363314 : x ≠ y ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq41528
  have eq363315 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq363284
  have eq388818 : x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40865
       have i₂ := eq363315
       grind)
    | exact superpose eq363315 eq40865
    | exact resolve eq40865 eq363315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40865 eq363315
  have eq388914 : x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq388818
  have eq388961 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq388914
       have r₂ := eq363314
       grind)
    | exact resolve eq388914 eq363314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363314 eq388914
  have eq389133 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2429 y y
       have i₂ := eq388961
       grind)
    | exact superpose eq388961 eq2429
    | exact resolve eq2429 eq388961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388961
  have eq389159 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq389133
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq389133
    | exact resolve eq389133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389133
  have eq389160 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq389159
  have eq389596 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq389160 eq20
    | exact resolve eq20 eq389160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389678 : y = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq389160 eq1649
    | exact resolve eq1649 eq389160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq389848 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq389937 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq389678
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq389678
    | exact resolve eq389678 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq389678
  have eq390011 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq389596
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq389596
    | exact resolve eq389596 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389596
  have eq390014 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1599 eq389937
    | exact resolve eq389937 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599 eq389937
  have eq390052 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq390011 eq26
    | exact resolve eq26 eq390011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390126 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq390011 eq2418
    | exact resolve eq2418 eq390011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq390911 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq390014 eq1654
    | exact resolve eq1654 eq390014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654 eq390014
  have eq391031 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq390911
       have r₂ := eq389160
       grind)
    | exact resolve eq390911 eq389160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390911
  have eq391644 : y = (k y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq389160 eq391031
    | exact resolve eq391031 eq389160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389160
  have eq391687 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq391031 eq887
    | (have j0 := eq887 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq887 eq391031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq391031
  have eq391692 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq391687
  have eq391706 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq391692
    | exact resolve eq391692 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391692
  have eq391742 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq391644
       have r₂ := eq389848
       grind)
    | exact resolve eq391644 eq389848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389848 eq391644
  have eq391745 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq391706
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq391706
    | exact resolve eq391706 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391706
  have eq391774 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq391745
       have r₂ := eq390011
       grind)
    | exact resolve eq391745 eq390011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391745
  have eq391800 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq391774
    | exact resolve eq391774 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391774
  have eq392047 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26736
       have i₂ := eq391742
       grind)
    | exact superpose eq391742 eq26736
    | exact resolve eq26736 eq391742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26736 eq391742
  have eq392173 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq392047
  have eq392207 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq392173
       have r₂ := eq36558
       grind)
    | exact resolve eq392173 eq36558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36558 eq392173
  have eq392767 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq391800 eq1079
    | exact resolve eq1079 eq391800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq391800
  have eq423135 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq390126 eq392767
    | exact resolve eq392767 eq390126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390126 eq392767
  have eq423259 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq423135
  have eq423330 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq423259
       have i₂ := eq1167 sF4 sF1
       grind)
    | exact superpose eq1167 eq423259
    | exact resolve eq423259 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq423259
  have eq437359 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq423330 eq2280
    | exact resolve eq2280 eq423330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280 eq423330
  have eq511693 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq392207
       grind)
    | exact superpose eq392207 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq392207
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq392207
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq392207
       grind)
    | exact resolve eq13 eq392207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392207
  have eq511725 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq511693
  have eq511765 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq511725
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq511725
    | exact resolve eq511725 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511725
  have eq515867 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7031 x
       have i₂ := eq511765
       grind)
    | exact superpose eq511765 eq7031
    | (have j0 := eq7031 x
       grind)
    | exact resolve eq7031 eq511765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7031 eq511765
  have eq515947 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq515867
    | exact resolve eq515867 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515867
  have eq515991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq515947
       have r₂ := eq390011
       grind)
    | exact resolve eq515947 eq390011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390011 eq515947
  have eq516026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq515991
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq515991
    | exact resolve eq515991 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515991
  have eq516059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq516026
    | exact resolve eq516026 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516026
  have eq516096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq516059
    | exact resolve eq516059 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516059
  have eq516122 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq516096
       have r₂ := eq27
       grind)
    | exact resolve eq516096 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516096
  have eq516138 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq516122
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq516122
    | exact resolve eq516122 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516122
  have eq516146 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq516138
    | exact resolve eq516138 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516138
  have eq516147 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq516146
  have eq516669 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq516147 eq437359
    | exact resolve eq437359 eq516147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437359 eq516147
  have eq516718 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq516669
  have eq518500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq516718 eq390052
    | exact resolve eq390052 eq516718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390052 eq516718
  have eq518573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq518500
  have eq518609 : x = (M.op x y) := by
    first
    | (have r₁ := eq518573
       have r₂ := eq27
       grind)
    | exact resolve eq518573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518573
  have eq518618 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq518609 eq20
    | exact resolve eq20 eq518609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq518727 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq518609 eq2424
    | exact resolve eq2424 eq518609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq518913 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq518727
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq518727
    | exact resolve eq518727 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq518727
  have eq518997 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq518618
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq518618
    | exact resolve eq518618 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518618
  have eq519000 : x = (M.op y y) := by
    first
    | exact superpose eq518609 eq518913
    | exact resolve eq518913 eq518609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518913
  have eq519719 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq518997 eq26
    | exact resolve eq26 eq518997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq520622 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18099
       have i₂ := eq519000
       grind)
    | exact superpose eq519000 eq18099
    | exact resolve eq18099 eq519000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18099
  have eq520753 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq519000
       grind)
    | exact superpose eq519000 eq13
    | exact resolve eq13 eq519000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519000
  have eq520826 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq520622
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq520622
    | exact resolve eq520622 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520622
  have eq520847 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq518997 eq520826
    | exact resolve eq520826 eq518997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520826
  have eq534035 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq520847 eq6189
    | exact resolve eq6189 eq520847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6189
  have eq534307 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq520847 eq2429
    | exact resolve eq2429 eq520847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429 eq520847
  have eq534329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq519719 eq534307
    | exact resolve eq534307 eq519719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534307
  have eq534367 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq534035
    | exact resolve eq534035 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq534035
  have eq534371 : x = y := by
    first
    | (have r₁ := eq534329
       have r₂ := eq27
       grind)
    | exact resolve eq534329 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534329
  have eq534397 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq518609 eq534367
    | exact resolve eq534367 eq518609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518609 eq534367
  have eq534408 : x = (k y y) := by
    first
    | (have r₁ := eq534397
       have r₂ := eq520753
       grind)
    | exact resolve eq534397 eq520753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520753 eq534397
  have eq535229 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq534371
       grind)
    | exact superpose eq534371 eq24
    | exact resolve eq24 eq534371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq536016 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq535229
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq535229
    | exact resolve eq535229 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535229
  have eq536197 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq518997 eq536016
    | exact resolve eq536016 eq518997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536016
  have eq536977 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq536197 eq519719
    | exact resolve eq519719 eq536197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519719 eq536197
  have eq537338 : x = (k x x) := by
    first
    | (have i₁ := eq534408
       have i₂ := eq534371
       grind)
    | exact superpose eq534371 eq534408
    | exact resolve eq534408 eq534371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534371 eq534408
  have eq537398 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq900 x x
       have i₂ := eq537338
       grind)
    | exact superpose eq537338 eq900
    | (have j0 := eq900 x x
       grind)
    | exact resolve eq900 eq537338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq537338
  have eq537404 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq537398
  have eq537405 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq537404
  have eq537432 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq537405
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq537405
    | exact resolve eq537405 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq537405
  have eq537474 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq518997 eq537432
    | exact resolve eq537432 eq518997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518997 eq537432
  have eq540168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq537474 eq536977
    | exact resolve eq536977 eq537474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536977 eq537474
  have eq540169 : False := by grind
  exact eq540169

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq50
    | exact resolve eq50 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq102 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq103 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq107 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq103
    | exact resolve eq103 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq109 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq107
    | exact resolve eq107 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq107
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq102
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq118 : (M.op y x) = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq117
    | exact resolve eq117 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq146 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq16
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq250 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq250 eq14
    | exact resolve eq14 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq610 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq605
    | exact resolve eq605 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq612 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq603 X0 X1 X2 X3
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq603
    | exact resolve eq603 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq619 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq589 X0 X1 X2 X3 X4
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq589
    | exact resolve eq589 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq654 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq51
    | exact resolve eq51 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1897 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq533 (M.op x sF4) (M.op x sF4)
       have i₂ := eq14 (M.op x sF4) sF4 x
       grind)
    | exact superpose eq14 eq533
    | exact resolve eq533 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1907 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1897 X0
       have i₂ := eq54 X0 sF4
       grind)
    | exact superpose eq54 eq1897
    | exact resolve eq1897 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq2100 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq563 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq563 X0 X0 X0
       grind)
    | exact superpose eq563 eq563
    | exact resolve eq563 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2123 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq563 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq563 X0 X0 X0
       grind)
    | exact superpose eq563 eq563
    | exact resolve eq563 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2158 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq563 X0 X0 X0
       grind)
    | exact superpose eq563 eq14
    | exact resolve eq14 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2160 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq563 X0 X0 X0
       grind)
    | exact superpose eq563 eq51
    | exact resolve eq51 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2161 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq563 X0 X0 X0
       grind)
    | exact superpose eq563 eq52
    | exact resolve eq52 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2172 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq521 (M.op x (M.op x x))
       have i₂ := eq563 x x x
       grind)
    | exact superpose eq563 eq521
    | exact resolve eq521 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq2175 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq599 (M.op x (M.op x x)) x
       have i₂ := eq563 x x x
       grind)
    | exact superpose eq563 eq599
    | exact resolve eq599 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq2374 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq530 X0
       have i₂ := eq2160 X0
       grind)
    | exact superpose eq2160 eq530
    | exact resolve eq530 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2406 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq2160 eq533
    | exact resolve eq533 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2419 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq533 eq2406
    | exact resolve eq2406 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq2406
  have eq2458 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq654 eq2374
    | exact resolve eq2374 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq2374
  have eq2579 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2161 X0
       have i₂ := eq2160 X0
       grind)
    | exact superpose eq2160 eq2161
    | exact resolve eq2161 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq2702 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2172 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2172
    | exact resolve eq2172 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172
  have eq2750 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2702 X0 X1
       have i₂ := eq2160 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq2160 eq2702
    | exact resolve eq2702 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq2766 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2750 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2750
    | exact resolve eq2750 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq2908 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq27 eq2175
    | (have j0 := eq2175 (σ y) (σ x)
       grind)
    | exact resolve eq2175 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2974 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2908
       have i₂ := eq2160 sF3
       grind)
    | exact superpose eq2160 eq2908
    | exact resolve eq2908 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908
  have eq6651 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq588
    | exact resolve eq588 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq6712 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq250 eq6651
    | exact resolve eq6651 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6651
  have eq6938 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq612 X0 X1 X2 X3
       have i₂ := eq610 X0 X1
       grind)
    | exact superpose eq610 eq612
    | exact resolve eq612 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq7198 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6938 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq563 x X1 X0
       grind)
    | exact superpose eq563 eq6938
    | exact resolve eq6938 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq7221 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6938 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq6938
    | exact resolve eq6938 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7276 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X2)) X2 X1
       have i₂ := eq6938 X0 (M.op X1 X2) (M.op X1 X2) X0
       grind)
    | exact superpose eq6938 eq14
    | exact resolve eq14 eq6938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6938
  have eq8856 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq619 X0 X1 X2 X3 X4
       have i₂ := eq610 X0 X1
       grind)
    | exact superpose eq610 eq619
    | exact resolve eq619 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq619
  have eq9035 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8856 X0 (M.op X0 (M.op X0 X0)) X2 X3 x
       have i₂ := eq530 X0
       grind)
    | exact superpose eq530 eq8856
    | exact resolve eq8856 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq8856
  have eq31887 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq588 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq2158 X0 X0 X1
       grind)
    | exact superpose eq2158 eq588
    | exact resolve eq588 eq2158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31990 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31887 X0 X1 x x x
       have i₂ := eq588 X0 X0 x x x
       grind)
    | exact superpose eq588 eq31887
    | exact resolve eq31887 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq31887
  have eq33215 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq6712 eq2158
    | exact resolve eq2158 eq6712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2158 eq6712
  have eq33261 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1907 eq33215
    | exact resolve eq33215 eq1907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907 eq33215
  have eq33264 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2579 eq33261
    | exact resolve eq33261 eq2579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579 eq33261
  have eq46849 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2766 eq14
    | exact resolve eq14 eq2766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq47786 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2100 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2100
    | (have j0 := eq2100 y x X0
       grind)
    | exact resolve eq2100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq50144 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq2123
    | (have j0 := eq2123 (σ y) X0 (σ x)
       grind)
    | exact resolve eq2123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50759 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq50144 X0
       have i₂ := eq2160 sF3
       grind)
    | exact superpose eq2160 eq50144
    | exact resolve eq50144 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160 eq50144
  have eq74141 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq47786 y
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq47786
    | exact resolve eq47786 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq47786
  have eq74305 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74141
       have i₂ := eq31990 (M.op y x) y
       grind)
    | exact superpose eq31990 eq74141
    | exact resolve eq74141 eq31990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74141
  have eq74344 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74305
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq74305
    | exact resolve eq74305 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq74305
  have eq74362 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq46849 eq74344
    | exact resolve eq74344 eq46849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46849 eq74344
  have eq101819 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X0 (M.op X0 X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7221 X2 (M.op X1 X0) (M.op x (M.op X1 X1)) X3
       have i₂ := eq2123 X0 x X1
       grind)
    | exact superpose eq2123 eq7221
    | exact resolve eq7221 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123
  have eq102711 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq7221 eq101819
    | exact resolve eq101819 eq7221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101819
  have eq114701 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7198 eq7276
    | exact resolve eq7276 eq7198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7198
  have eq114727 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X3)))) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq7276 eq7221
    | exact resolve eq7221 eq7276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7276
  have eq114946 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq7221 eq114727
    | exact resolve eq114727 eq7221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114727
  have eq118593 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7221 X2 (M.op X1 X0) (M.op (M.op x x) (M.op X1 X1)) X3
       have i₂ := eq9035 X0 x x X1
       grind)
    | exact superpose eq9035 eq7221
    | exact resolve eq7221 eq9035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9035
  have eq118631 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq7221 eq118593
    | exact resolve eq118593 eq7221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7221 eq118593
  have eq168410 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq50759 eq114701
    | exact resolve eq114701 eq50759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50759 eq114701
  have eq169188 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq168410
       have i₂ := eq118631 sF2 sF2 (M.op sF4 sF4)
       grind)
    | exact superpose eq118631 eq168410
    | exact resolve eq168410 eq118631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168410
  have eq169526 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq250 eq169188
    | exact resolve eq169188 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq169188
  have eq169703 : (σ y) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2974 eq169526
    | exact resolve eq169526 eq2974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974 eq169526
  have eq170426 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq169703
       have i₂ := eq118631 sF2 sF0 (M.op sF3 sF4)
       grind)
    | exact superpose eq118631 eq169703
    | exact resolve eq169703 eq118631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169703
  have eq253443 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq74362 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq74362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74362
  have eq253444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq253443
    | exact resolve eq253443 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253443
  have eq253455 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq253444
       have r₂ := eq28
       grind)
    | exact resolve eq253444 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253444
  have eq254182 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq253455 eq33264
    | exact resolve eq33264 eq253455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33264
  have eq254350 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq253455 eq260
    | exact resolve eq260 eq253455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq254430 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ y) (σ x)))) X0) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq253455 eq114946
    | exact resolve eq114946 eq253455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254439 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by grind
  have eq254447 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq114946 eq254430
    | exact resolve eq254430 eq114946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114946 eq254430
  have eq254488 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq254350
       have i₂ := eq102711 sF2 sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq102711 eq254350
    | exact resolve eq254350 eq102711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254350
  have eq254587 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq254182
       have i₂ := eq102711 sF2 sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq102711 eq254182
    | exact resolve eq254182 eq102711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102711 eq254182
  have eq254619 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq254488
       have i₂ := eq118631 sF2 sF2 (M.op sF3 sF4)
       grind)
    | exact superpose eq118631 eq254488
    | exact resolve eq254488 eq118631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254488
  have eq254674 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq254587
       have i₂ := eq118631 sF2 sF2 (M.op sF3 sF4)
       grind)
    | exact superpose eq118631 eq254587
    | exact resolve eq254587 eq118631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118631 eq254587
  have eq254681 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq170426 eq254619
    | exact resolve eq254619 eq170426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254619
  have eq254705 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq170426 eq254674
    | exact resolve eq254674 eq170426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170426 eq254674
  have eq254712 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq253455 eq254681
    | exact resolve eq254681 eq253455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253455 eq254681
  have eq254989 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq254712
  have eq255099 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq254989
       have r₂ := eq254439
       grind)
    | exact resolve eq254989 eq254439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254439 eq254989
  have eq258363 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq254447 eq255099
    | exact resolve eq255099 eq254447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254447 eq255099
  have eq258972 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq258363
  have eq259556 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq258972 eq51
    | exact resolve eq51 eq258972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq258972
  have eq280046 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq259556 eq254705
    | exact resolve eq254705 eq259556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254705 eq259556
  have eq280189 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq280046
  have eq280327 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq280189 eq146
    | exact resolve eq146 eq280189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq280189
  have eq280743 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq29 eq280327
    | exact resolve eq280327 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280327
  have eq280744 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq280743
  have eq281137 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31990 y y
       have i₂ := eq280744
       grind)
    | exact superpose eq280744 eq31990
    | exact resolve eq31990 eq280744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31990 eq280744
  have eq281172 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq281137
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq281137
    | exact resolve eq281137 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281137
  have eq281429 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq281172 eq30
    | exact resolve eq30 eq281172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq281172
  have eq281795 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq281429
    | exact resolve eq281429 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq281429
  have eq281796 : x = (M.op x y) ∨ x = y := by grind
  clear eq281795
  have eq281837 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq281796 eq21
    | exact resolve eq21 eq281796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281956 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq281796 eq2419
    | exact resolve eq2419 eq281796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419 eq281796
  have eq282319 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq281956
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq281956
    | exact resolve eq281956 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281956
  have eq282390 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq281837
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq281837
    | exact resolve eq281837 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281837
  have eq282444 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq282390 eq27
    | exact resolve eq27 eq282390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282390
  have eq282807 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2458 y
       have i₂ := eq282319
       grind)
    | exact superpose eq282319 eq2458
    | exact resolve eq2458 eq282319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2458 eq282319
  have eq283028 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq282807
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq282807
    | exact resolve eq282807 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282807
  have eq283125 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq283028
    | exact resolve eq283028 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283028
  have eq284002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq283125 eq282444
    | exact resolve eq282444 eq283125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282444 eq283125
  have eq284107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq284002
  have eq284155 : x = y := by
    first
    | (have r₁ := eq284107
       have r₂ := eq28
       grind)
    | exact resolve eq284107 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284107
  have eq284178 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq284155
       grind)
    | exact superpose eq284155 eq19
    | exact resolve eq19 eq284155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq284179 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq284155
       grind)
    | exact superpose eq284155 eq25
    | exact resolve eq25 eq284155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq284155
  have eq284712 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq284179
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq284179
    | exact resolve eq284179 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq284179
  have eq284794 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq284712 eq27
    | exact resolve eq27 eq284712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq284712
  have eq286052 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq284794 eq72
    | exact resolve eq72 eq284794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq284794
  have eq286503 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq286052
       have i₂ := eq284178
       grind)
    | exact superpose eq284178 eq286052
    | exact resolve eq286052 eq284178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284178 eq286052
  have eq286731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq286503 eq15
    | exact resolve eq15 eq286503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286503
  have eq287087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq286731
    | exact resolve eq286731 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq286731
  have eq287213 : False := by grind
  exact eq287213

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_y_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq10
    | exact resolve eq10 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq63 sF2
       grind)
    | exact superpose eq63 eq49
    | exact resolve eq49 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq67
    | exact resolve eq67 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq65
    | exact resolve eq65 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq95 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq95
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq241 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq63 (τ X0)
       grind)
    | exact superpose eq63 eq34
    | exact resolve eq34 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq312 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq301 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq301
    | exact resolve eq301 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq315 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq312 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq312
    | exact resolve eq312 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq312
  have eq430 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq432 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
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
  clear eq53
  have eq456 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  clear eq52
  have eq633 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq50
    | exact resolve eq50 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq898 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq315 X0
       grind)
    | exact superpose eq315 eq16
    | exact resolve eq16 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq1055 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq898 X0
       grind)
    | exact superpose eq898 eq50
    | exact resolve eq50 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq1389 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq241 eq243
    | exact resolve eq243 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1426 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq243 eq50
    | exact resolve eq50 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1427 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq243 eq51
    | exact resolve eq51 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq1448 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq241 eq1427
    | exact resolve eq1427 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1449 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq241 eq1426
    | exact resolve eq1426 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq1426
  have eq1779 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq456 X0 X0 X0
       grind)
    | exact superpose eq456 eq50
    | exact resolve eq50 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1780 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq456 X0 X0 X0
       grind)
    | exact superpose eq456 eq51
    | exact resolve eq51 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq456
  have eq1958 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1448 eq1449
    | exact resolve eq1449 eq1448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq2059 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq430 X0
       have i₂ := eq1779 X0
       grind)
    | exact superpose eq1779 eq430
    | exact resolve eq430 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq2086 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1779 eq432
    | exact resolve eq432 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq2097 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq432 eq2086
    | exact resolve eq2086 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086
  have eq2136 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq633 eq2059
    | exact resolve eq2059 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq2346 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1780 eq432
    | exact resolve eq432 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq2357 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq432 eq2346
    | exact resolve eq2346 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432 eq2346
  have eq3051 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq1055 eq2059
    | exact resolve eq2059 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq26584 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1448 eq1389
    | exact resolve eq1389 eq1448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389 eq1448
  have eq26585 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1958 eq26584
    | exact resolve eq26584 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq26584
  have eq37372 : y = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op x x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26585 y
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq26585
    | exact resolve eq26585 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq37421 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26585 eq37372
    | exact resolve eq37372 eq26585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26585 eq37372
  have eq37502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37421 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq37421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37421
  have eq37503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq37502
    | exact resolve eq37502 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37502
  have eq37514 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq37503
       have r₂ := eq27
       grind)
    | exact resolve eq37503 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37503
  have eq37518 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq37514
    | exact resolve eq37514 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37514
  have eq37568 : (τ (σ y)) = (M.op y (M.op (M.op x y) (τ (M.op (σ x) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37518 eq1055
    | exact resolve eq1055 eq37518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37518
  have eq37676 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1055 eq37568
    | exact resolve eq37568 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055 eq37568
  have eq37710 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq37676
    | exact resolve eq37676 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37676
  have eq37715 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq37710
    | exact resolve eq37710 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37710
  have eq37716 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq37715
  have eq37768 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37716 eq2357
    | exact resolve eq2357 eq37716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357
  have eq37788 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq37768
    | exact resolve eq37768 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37768
  have eq37871 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37788 eq3051
    | exact resolve eq3051 eq37788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051 eq37788
  have eq37933 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq37871
    | exact resolve eq37871 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq37871
  have eq38995 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37716 eq37933
    | exact resolve eq37933 eq37716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37716 eq37933
  have eq39038 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq38995
  have eq39047 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq39038
    | exact resolve eq39038 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq39038
  have eq39050 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39047
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39047
    | exact resolve eq39047 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39047
  have eq39051 : x = (M.op x y) ∨ x = y := by grind
  clear eq39050
  have eq39053 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq39051 eq20
    | exact resolve eq20 eq39051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39158 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq39051 eq2097
    | exact resolve eq2097 eq39051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097 eq39051
  have eq39201 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq39158
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39158
    | exact resolve eq39158 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39158
  have eq39257 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq39053
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39053
    | exact resolve eq39053 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39053
  have eq39277 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq39257 eq26
    | exact resolve eq26 eq39257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39257
  have eq39514 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2136 y
       have i₂ := eq39201
       grind)
    | exact superpose eq39201 eq2136
    | exact resolve eq2136 eq39201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2136 eq39201
  have eq39578 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq39514
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39514
    | exact resolve eq39514 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39514
  have eq39621 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq39578
    | exact resolve eq39578 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39578
  have eq39910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq39621 eq39277
    | exact resolve eq39277 eq39621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39277 eq39621
  have eq39953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq39910
  have eq39961 : x = y := by
    first
    | (have r₁ := eq39953
       have r₂ := eq27
       grind)
    | exact resolve eq39953 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39953
  have eq39964 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq39961
       grind)
    | exact superpose eq39961 eq18
    | exact resolve eq18 eq39961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq39965 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq39961
       grind)
    | exact superpose eq39961 eq24
    | exact resolve eq24 eq39961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq39961
  have eq40171 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq39965
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39965
    | exact resolve eq39965 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39965
  have eq40202 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40171 eq26
    | exact resolve eq26 eq40171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq40171
  have eq40740 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq40202 eq68
    | exact resolve eq68 eq40202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq40202
  have eq40938 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40740
       have i₂ := eq39964
       grind)
    | exact superpose eq39964 eq40740
    | exact resolve eq40740 eq39964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39964 eq40740
  have eq41015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40938 eq15
    | exact resolve eq15 eq40938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40938
  have eq41116 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq41015
    | exact resolve eq41015 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq41015
  have eq41154 : False := by grind
  exact eq41154
