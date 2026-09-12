import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3296`: `x ◇ x = y ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyy_pxx_pxy_Equation3296 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3296 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3296.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
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
  clear eq23
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
  have eq53 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x (M.op x y))) := by
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
  have eq54 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X1 X0)) X2 X3
       have i₂ := eq14 X0 X3 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq56 X0 x X2 X3
       have i₂ := eq14 X0 (M.op x (M.op x X0)) x
       grind)
    | (have i₁ := eq56 X0 x X2 X3
       have i₂ := eq14 (M.op x (M.op x X0)) x X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq86 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq90 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq90
  have eq93 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq86
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq103
  have eq126 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq108
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq126
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq157 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq140
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq140
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq140 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq157
  have eq184 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq163
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq163
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq184
  have eq217 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq426 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq57 X1 x X3
       have i₂ := eq57 X1 x X0
       grind)
    | (have i₁ := eq57 X0 X0 x
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op X1 X0) X1 X2
       have i₂ := eq14 X0 (M.op X1 (M.op X1 X0)) X1
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) = (M.op X4 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 (M.op X3 X1) X2 X4
       have i₂ := eq57 X1 X3 X0
       grind)
    | (have i₁ := eq57 (M.op X0 X0) X1 X2
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq57 y X0 x
       have i₂ := eq217 x
       grind)
    | exact superpose eq217 eq57
    | exact resolve eq57 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq482 : ∀ X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq444 x X1 X2 X3 x
       have i₂ := eq59 X1 x x
       grind)
    | (have i₁ := eq444 x X1 X2 X3 (M.op x (M.op X1 X1))
       have i₂ := eq59 (M.op x (M.op X1 X1)) X2 X3
       grind)
    | exact superpose eq59 eq444
    | exact resolve eq444 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq444
  have eq1850 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (σ X2)))) = (σ (k X2 X2)) ∨ (σ X2) = (M.op X0 (M.op X1 (M.op X1 (σ X2)))) ∨ (σ X2) = (M.op X0 (M.op X1 (M.op X1 (σ X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X0
       have i₂ := eq14 (σ X0) X1 X2
       grind)
    | exact superpose eq14 eq80
    | exact resolve eq80 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1886 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (σ X2)))) = (σ (k X2 X2)) ∨ (σ X2) = (M.op X0 (M.op X1 (M.op X1 (σ X2)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1850 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq9062 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq9088 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq50 eq9062
    | exact resolve eq9062 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9062
  have eq9091 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq9088
       have r₂ := eq13 x x
       grind)
    | exact resolve eq9088 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9088
  have eq9092 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq9091
       grind)
    | exact superpose eq9091 eq44
    | exact resolve eq44 eq9091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq9772 : (M.op y y) = (τ (k (σ y) (σ y))) ∨ y = (M.op y y) := by
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
  have eq9804 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq108 eq9772
    | exact resolve eq9772 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9772
  have eq9807 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq9804
       have r₂ := eq13 x y
       grind)
    | exact resolve eq9804 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9804
  have eq9808 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq9807
       grind)
    | exact superpose eq9807 eq78
    | exact resolve eq78 eq9807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11125 : (M.op (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq164 eq16
    | exact resolve eq16 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq11167 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq163 eq11125
    | exact resolve eq11125 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq11125
  have eq11172 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq11167
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq11167 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11167
  have eq11174 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq11172 eq140
    | exact resolve eq140 eq11172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq17491 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq9091
       grind)
    | exact superpose eq9091 eq92
    | exact resolve eq92 eq9091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq17493 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq128
       have i₂ := eq9807
       grind)
    | exact superpose eq9807 eq128
    | exact resolve eq128 eq9807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq17494 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11172 eq186
    | exact resolve eq186 eq11172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq11172
  have eq18844 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17491 eq15
    | exact resolve eq15 eq17491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17491
  have eq18894 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18844
       have i₂ := eq9092
       grind)
    | exact superpose eq9092 eq18844
    | exact resolve eq18844 eq9092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9092 eq18844
  have eq18897 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq18894
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq18894 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18894
  have eq18902 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq18897 eq50
    | exact resolve eq50 eq18897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq18897
  have eq18919 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq18902
       have i₂ := eq9091
       grind)
    | exact superpose eq9091 eq18902
    | exact resolve eq18902 eq9091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9091 eq18902
  have eq19222 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq17493 eq15
    | exact resolve eq15 eq17493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17493
  have eq19276 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19222
       have i₂ := eq9808
       grind)
    | exact superpose eq9808 eq19222
    | exact resolve eq19222 eq9808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19222
  have eq19279 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq19276
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq19276 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19276
  have eq19284 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq19279 eq108
    | exact resolve eq108 eq19279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq19303 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq19284
       have i₂ := eq9807
       grind)
    | exact superpose eq9807 eq19284
    | exact resolve eq19284 eq9807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19284
  have eq19906 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17494 eq15
    | exact resolve eq15 eq17494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17494
  have eq19960 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11174 eq19906
    | exact resolve eq19906 eq11174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19906
  have eq19965 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq19960
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq19960 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19960
  have eq27502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq27503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq27502
    | exact resolve eq27502 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27502
  have eq27514 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq27503
       have r₂ := eq28
       grind)
    | exact resolve eq27503 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27503
  have eq27852 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27514 eq19303
    | exact resolve eq19303 eq27514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19303 eq27514
  have eq27931 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq27852
    | exact resolve eq27852 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27852
  have eq27932 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq27931
  have eq27961 : (τ (σ y)) = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27932 eq18919
    | exact resolve eq18919 eq27932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18919 eq27932
  have eq28029 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq27961
    | exact resolve eq27961 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq27961
  have eq28030 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq28029
  have eq28052 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq217 X0
       have i₂ := eq28030
       grind)
    | exact superpose eq28030 eq217
    | exact resolve eq217 eq28030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq28101 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op X0 y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq482 y x y
       have i₂ := eq28030
       grind)
    | exact superpose eq28030 eq482
    | exact resolve eq482 eq28030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq28030
  have eq28116 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq28101 x
       have i₂ := eq447 x
       grind)
    | (have i₁ := eq28101 x
       have i₂ := eq447 x
       grind)
    | exact superpose eq447 eq28101
    | (have j0 := eq28101 x
       grind)
    | exact resolve eq28101 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq28101
  have eq29430 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28052 eq28116
    | exact resolve eq28116 eq28052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28052 eq28116
  have eq29506 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq29430 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29430
  have eq29630 : ∀ X0 X1 : G, y = (M.op X0 (M.op x y)) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X1 x
       have i₂ := eq29506 X0
       grind)
    | exact superpose eq29506 eq14
    | (have j1 := eq29506 X1
       grind)
    | exact resolve eq14 eq29506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29506
  have eq29676 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ y = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq29630 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29630
    | (have j0 := eq29630 X0 X1
       grind)
    | exact resolve eq29630 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29630
  have eq29859 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29676 X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29676
    | (have j0 := eq29676 X0 x
       grind)
    | exact resolve eq29676 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29676
  have eq29984 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29859 eq426
    | exact resolve eq426 eq29859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30029 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29859 eq11174
    | exact resolve eq11174 eq29859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11174 eq29859
  have eq30046 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19965 eq30029
    | exact resolve eq30029 eq19965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19965 eq30029
  have eq30071 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30046
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30046
    | exact resolve eq30046 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30046
  have eq30122 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq30071 eq426
    | exact resolve eq426 eq30071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq30071
  have eq31890 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29984 X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29984
    | (have j0 := eq29984 X0 x
       grind)
    | exact resolve eq29984 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29984
  have eq32150 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9808
       have i₂ := eq31890 y
       grind)
    | exact superpose eq31890 eq9808
    | exact resolve eq9808 eq31890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31890
  have eq32176 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19279 eq32150
    | exact resolve eq32150 eq19279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32150
  have eq32201 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq32176
    | exact resolve eq32176 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32176
  have eq34211 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27 eq30122
    | (have j0 := eq30122 X0 (σ x)
       grind)
    | exact resolve eq30122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30122
  have eq34505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34211 eq32201
    | exact resolve eq32201 eq34211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32201 eq34211
  have eq34506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq34505
  have eq34514 : y = (M.op x y) := by
    first
    | (have r₁ := eq34506
       have r₂ := eq28
       grind)
    | exact resolve eq34506 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34506
  have eq34538 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq34514 eq21
    | exact resolve eq21 eq34514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq34540 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq34514 eq53
    | exact resolve eq53 eq34514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq34703 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq34540 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34540
    | (have j0 := eq34540 X0
       grind)
    | exact resolve eq34540 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34540
  have eq34705 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq34538
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34538
    | exact resolve eq34538 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34538
  have eq34749 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq34514 eq34703
    | exact resolve eq34703 eq34514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34703
  have eq34785 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq34705 eq27
    | exact resolve eq27 eq34705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq35489 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq34749 X0
       have i₂ := eq34749 X1
       grind)
    | (have i₁ := eq34749 X0
       have i₂ := eq34749 y
       grind)
    | exact superpose eq34749 eq34749
    | exact resolve eq34749 eq34749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34749
  have eq35861 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq19
       have i₂ := eq35489 X0 x
       grind)
    | (have i₁ := eq19
       have i₂ := eq35489 x X0
       grind)
    | exact superpose eq35489 eq19
    | (have j1 := eq35489 X0 x
       grind)
    | exact resolve eq19 eq35489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq35489
  have eq35893 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq34514 eq35861
    | exact resolve eq35861 eq34514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34514 eq35861
  have eq36073 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9808
       have i₂ := eq35893 y
       grind)
    | exact superpose eq35893 eq9808
    | exact resolve eq9808 eq35893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9808
  have eq36094 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19279 eq36073
    | exact resolve eq36073 eq19279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36073
  have eq36152 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq34705 eq36094
    | exact resolve eq36094 eq34705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36094
  have eq36194 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq36152
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36152
    | exact resolve eq36152 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq36152
  have eq36226 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq34705 eq36194
    | exact resolve eq36194 eq34705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36194
  have eq38066 : ∀ X0 X1 : G, (σ (k (k y y) (k y y))) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) ∨ (k (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1886 X0 X1 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq1886
    | exact resolve eq1886 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq38452 : ∀ X0 X1 : G, (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (σ (k (k y y) (k y y))) ∨ (k (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq38066 (M.op X1 (M.op X1 (k sF3 sF3))) X1
       have i₂ := eq14 (M.op X1 (M.op X1 (k sF3 sF3))) X1 x
       grind)
    | (have i₁ := eq38066 X1 x
       have i₂ := eq14 (k sF3 sF3) X1 x
       grind)
    | exact superpose eq14 eq38066
    | (have j0 := eq38066 X0 X1
       grind)
    | exact resolve eq38066 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38066
  have eq38618 : ∀ X0 X1 : G, (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (σ (k (M.op y y) (M.op y y))) ∨ (k (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq38452 X0 X1
       have i₂ := eq9807
       grind)
    | exact superpose eq9807 eq38452
    | (have j0 := eq38452 X0 X1
       grind)
    | exact resolve eq38452 eq9807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9807 eq38452
  have eq38751 : ∀ X0 X1 : G, (σ (k y y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq38618 X0 X1
       have i₂ := eq35893 y
       grind)
    | exact superpose eq35893 eq38618
    | (have j0 := eq38618 X0 X1
       grind)
    | exact resolve eq38618 eq35893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35893 eq38618
  have eq38860 : ∀ X0 X1 : G, (σ (k y y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq19279 eq38751
    | (have j0 := eq38751 X0 X1
       grind)
    | exact resolve eq38751 eq19279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38751
  have eq38947 : ∀ X0 X1 : G, (σ (k y y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq222 eq38860
    | (have j0 := eq38860 X0 X1
       grind)
    | exact resolve eq38860 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38860
  have eq39027 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq38947 X0 X1
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq38947
    | (have j0 := eq38947 X0 X1
       grind)
    | exact resolve eq38947 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq38947
  have eq39101 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq19279 eq39027
    | (have j0 := eq39027 X0 X1
       grind)
    | exact resolve eq39027 eq19279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39027
  have eq39171 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq34705 eq39101
    | (have j0 := eq39101 X0 X1
       grind)
    | exact resolve eq39101 eq34705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39101
  have eq39236 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq36226 eq39171
    | (have j0 := eq39171 X0 X1
       grind)
    | exact resolve eq39171 eq36226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39171
  have eq39267 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq39236 (M.op x (M.op x (k sF3 sF3))) x
       have i₂ := eq14 (M.op x (M.op x (k sF3 sF3))) x x
       grind)
    | (have i₁ := eq39236 x x
       have i₂ := eq14 (k sF3 sF3) x x
       grind)
    | exact superpose eq14 eq39236
    | exact resolve eq39236 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39236
  have eq39292 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19279 eq39267
    | exact resolve eq39267 eq19279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19279 eq39267
  have eq39311 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq222 eq39292
    | exact resolve eq39292 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq39292
  have eq39319 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq34705 eq39311
    | exact resolve eq39311 eq34705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34705 eq39311
  have eq39323 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq36226 eq39319
    | exact resolve eq39319 eq36226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39319
  have eq39324 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq39323
  have eq39378 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq39324 eq427
    | exact resolve eq427 eq39324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq39324
  have eq39407 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq36226 eq39378
    | exact resolve eq39378 eq36226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36226 eq39378
  have eq39528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39407 eq34785
    | exact resolve eq34785 eq39407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34785 eq39407
  have eq39532 : False := by grind
  exact eq39532

/-- `Equation3296`: `x ◇ x = y ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pxx_pxy_Equation3296 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3296 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3296.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
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
  have eq53 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x (M.op x y))) := by
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
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X1 X0)) X2 X3
       have i₂ := eq14 X0 X3 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq56 X0 x X2 X3
       have i₂ := eq14 X0 (M.op x (M.op x X0)) x
       grind)
    | (have i₁ := eq56 X0 x X2 X3
       have i₂ := eq14 (M.op x (M.op x X0)) x X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq80 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq82 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq80 (σ X0)
       grind)
    | exact superpose eq80 eq10
    | exact resolve eq10 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq80 sF2
       grind)
    | exact superpose eq80 eq50
    | exact resolve eq50 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq85 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq84
       have i₂ := eq80 x
       grind)
    | exact superpose eq80 eq84
    | exact resolve eq84 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq82
    | exact resolve eq82 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq94 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq80 sF3
       grind)
    | exact superpose eq80 eq78
    | exact resolve eq78 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq95 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq94
       have i₂ := eq80 y
       grind)
    | exact superpose eq80 eq94
    | exact resolve eq94 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq108
    | exact resolve eq108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq120 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
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
  have eq139 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq80 sF1
       grind)
    | exact superpose eq80 eq136
    | exact resolve eq136 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq141 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq80 sF0
       grind)
    | exact superpose eq80 eq139
    | exact resolve eq139 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq139
  have eq232 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (σ X0) X2 x
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq59
    | exact resolve eq59 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq672 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) = (M.op X4 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 (M.op X3 X1) X2 X4
       have i₂ := eq57 X1 X3 X0
       grind)
    | (have i₁ := eq57 (M.op X0 X0) X1 X2
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq57 y X0 x
       have i₂ := eq232 x
       grind)
    | exact superpose eq232 eq57
    | exact resolve eq57 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq716 : ∀ X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq672 x X1 X2 X3 x
       have i₂ := eq59 X1 x x
       grind)
    | (have i₁ := eq672 x X1 X2 X3 (M.op x (M.op X1 X1))
       have i₂ := eq59 (M.op x (M.op X1 X1)) X2 X3
       grind)
    | exact superpose eq59 eq672
    | exact resolve eq672 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq672
  have eq11132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq11133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq11132
    | exact resolve eq11132 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11132
  have eq11144 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq11133
       have r₂ := eq28
       grind)
    | exact resolve eq11133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11133
  have eq11148 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq11144 eq120
    | exact resolve eq120 eq11144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq11144
  have eq11211 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq11148
    | exact resolve eq11148 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11148
  have eq11212 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11211
  have eq11239 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq232 X0
       have i₂ := eq11212
       grind)
    | exact superpose eq11212 eq232
    | exact resolve eq232 eq11212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq11264 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op X0 y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq716 y x y
       have i₂ := eq11212
       grind)
    | exact superpose eq11212 eq716
    | exact resolve eq716 eq11212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq11212
  have eq11271 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11264 x
       have i₂ := eq677 x
       grind)
    | (have i₁ := eq11264 x
       have i₂ := eq677 x
       grind)
    | exact superpose eq677 eq11264
    | (have j0 := eq11264 x
       grind)
    | exact resolve eq11264 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq11264
  have eq12146 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11239 eq11271
    | exact resolve eq11271 eq11239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11239 eq11271
  have eq12191 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq12146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12146
  have eq12248 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12191 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12191
    | (have j0 := eq12191 x
       grind)
    | exact resolve eq12191 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12191
  have eq12322 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12248 eq30
    | exact resolve eq30 eq12248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12248
  have eq12432 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq12322
    | exact resolve eq12322 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12322
  have eq12433 : y = (M.op x y) ∨ x = y := by grind
  clear eq12432
  have eq12448 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12433 eq21
    | exact resolve eq21 eq12433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12450 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12433 eq53
    | exact resolve eq53 eq12433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq12561 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12450 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12450
    | (have j0 := eq12450 X0
       grind)
    | exact resolve eq12450 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12450
  have eq12563 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12448
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12448
    | exact resolve eq12448 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12448
  have eq12579 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq12563 eq27
    | exact resolve eq27 eq12563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12563
  have eq13669 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq12433 eq12561
    | exact resolve eq12561 eq12433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12433
  have eq13759 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq13669 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13669
  have eq15224 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 y) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq12561 X1
       have i₂ := eq13759 X0
       grind)
    | (have i₁ := eq12561 X0
       have i₂ := eq13759 y
       grind)
    | exact superpose eq13759 eq12561
    | exact resolve eq12561 eq13759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12561 eq13759
  have eq15282 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 y) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq15224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15224
  have eq15602 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq15282 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15282
    | (have j0 := eq15282 x X0
       grind)
    | exact resolve eq15282 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15282
  have eq15803 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq15602 eq524
    | exact resolve eq524 eq15602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq15830 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq15602 eq141
    | exact resolve eq141 eq15602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq15602
  have eq15866 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq21 eq15830
    | exact resolve eq15830 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15830
  have eq15882 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq21 eq15803
    | (have j0 := eq15803 X0 X1
       grind)
    | exact resolve eq15803 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15803
  have eq22060 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq15866 eq15882
    | exact resolve eq15882 eq15866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15866 eq15882
  have eq22156 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq22060 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22060
  have eq22335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq22156 eq12579
    | exact resolve eq12579 eq22156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12579 eq22156
  have eq22336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq22335
  have eq22345 : x = y := by
    first
    | (have r₁ := eq22336
       have r₂ := eq28
       grind)
    | exact resolve eq22336 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22336
  have eq22383 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq22345
       grind)
    | exact superpose eq22345 eq19
    | exact resolve eq19 eq22345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq22384 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq22345
       grind)
    | exact superpose eq22345 eq25
    | exact resolve eq25 eq22345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22345
  have eq22488 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22384
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22384
    | exact resolve eq22384 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22384
  have eq22504 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22488 eq27
    | exact resolve eq27 eq22488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22488
  have eq22770 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq22504 eq85
    | exact resolve eq85 eq22504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq22504
  have eq22839 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq22770
       have i₂ := eq22383
       grind)
    | exact superpose eq22383 eq22770
    | exact resolve eq22770 eq22383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22383 eq22770
  have eq23637 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22839 eq15
    | exact resolve eq15 eq22839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22839
  have eq23683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq23637
    | exact resolve eq23637 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23637
  have eq23692 : False := by grind
  exact eq23692

/-- `Equation3296`: `x ◇ x = y ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pxy_Equation3296 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3296 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3296.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
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
  have eq53 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X3 (M.op X4 (M.op X4 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 X3 X4
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x (M.op x y))) := by
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
  have eq56 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X1 X0)) X2 X3
       have i₂ := eq14 X0 X3 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq58 X0 x X2 X3
       have i₂ := eq14 X0 (M.op x (M.op x X0)) x
       grind)
    | (have i₁ := eq58 X0 x X2 X3
       have i₂ := eq14 (M.op x (M.op x X0)) x X2
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq65 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq80
    | exact resolve eq80 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq92 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq106 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq102
  have eq107 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq106
  have eq138 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq16
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq400 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq226 eq14
    | exact resolve eq14 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq587 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) = (M.op X4 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59 (M.op X3 X1) X2 X4
       have i₂ := eq59 X1 X3 X0
       grind)
    | (have i₁ := eq59 (M.op X0 X0) X1 X2
       have i₂ := eq59 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq400 eq59
    | exact resolve eq59 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq400
  have eq627 : ∀ X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq587 x X1 X2 X3 x
       have i₂ := eq61 X1 x x
       grind)
    | (have i₁ := eq587 x X1 X2 X3 (M.op x (M.op X1 X1))
       have i₂ := eq61 (M.op x (M.op X1 X1)) X2 X3
       grind)
    | exact superpose eq61 eq587
    | exact resolve eq587 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq587
  have eq11641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11641
    | exact resolve eq11641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11641
  have eq11653 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq11642
       have r₂ := eq28
       grind)
    | exact resolve eq11642 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11642
  have eq11657 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11653
    | exact resolve eq11653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11653
  have eq11662 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11657 eq93
    | (have r₁ := eq93
       have r₂ := eq11657
       grind)
    | exact resolve eq93 eq11657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq11693 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11657 eq627
    | exact resolve eq627 eq11657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq11657
  have eq11697 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11662
  have eq11698 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11697
  have eq11701 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq594 eq11693
    | exact resolve eq11693 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq11693
  have eq13235 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11698 eq65
    | exact resolve eq65 eq11698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq13236 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11698 eq82
    | exact resolve eq82 eq11698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq11698
  have eq13245 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13236
  have eq13255 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq138 eq13235
    | exact resolve eq13235 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq13235
  have eq13257 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13255
       have r₂ := eq92
       grind)
    | exact resolve eq13255 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq13255
  have eq13259 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq13257
       grind)
    | exact superpose eq13257 eq49
    | exact resolve eq49 eq13257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq13257
  have eq13276 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13259
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq13259
    | exact resolve eq13259 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13259
  have eq13292 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13276 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq13276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13276
  have eq13293 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13292
  have eq13297 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq13293
    | exact resolve eq13293 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13293
  have eq13306 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq13297
    | exact resolve eq13297 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13297
  have eq13318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13245 eq11701
    | exact resolve eq11701 eq13245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11701 eq13245
  have eq13349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq13318
  have eq13361 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13349
       have r₂ := eq28
       grind)
    | exact resolve eq13349 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13349
  have eq13378 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq13361
       grind)
    | exact superpose eq13361 eq52
    | exact resolve eq52 eq13361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13398 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 x))) = (M.op X2 (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 x X2 x
       have i₂ := eq13361
       grind)
    | exact superpose eq13361 eq53
    | exact resolve eq53 eq13361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq13361
  have eq13431 : ∀ X0 X1 : G, (M.op y y) = (M.op X0 (M.op X1 (M.op X1 x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq55 eq13398
    | exact resolve eq13398 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq13398
  have eq13443 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq13378
    | exact resolve eq13378 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13378
  have eq13450 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13431 x x
       have i₂ := eq14 x x x
       grind)
    | (have i₁ := eq13431 (M.op x (M.op x x)) x
       have i₂ := eq14 (M.op x (M.op x x)) x x
       grind)
    | exact superpose eq14 eq13431
    | exact resolve eq13431 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13431
  have eq14006 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq13450
       grind)
    | exact superpose eq13450 eq107
    | exact resolve eq107 eq13450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq13450
  have eq14071 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14006
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq14006
    | exact resolve eq14006 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq14006
  have eq21762 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13306 eq14071
    | exact resolve eq14071 eq13306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13306 eq14071
  have eq21805 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21762
  have eq21859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21805 eq13443
    | exact resolve eq13443 eq21805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13443 eq21805
  have eq21905 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21859
  have eq21935 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq21905
       have r₂ := eq28
       grind)
    | exact resolve eq21905 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21905
  have eq21953 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq21935 eq30
    | exact resolve eq30 eq21935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq21935
  have eq22059 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq21953
    | exact resolve eq21953 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21953
  have eq22060 : x = y := by grind
  clear eq22059
  have eq22079 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq22060
       grind)
    | exact superpose eq22060 eq19
    | exact resolve eq19 eq22060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq22080 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq22060
       grind)
    | exact superpose eq22060 eq25
    | exact resolve eq25 eq22060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22060
  have eq22185 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22080
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22080
    | exact resolve eq22080 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22080
  have eq22200 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22185 eq27
    | exact resolve eq27 eq22185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22185
  have eq22446 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq22200 eq73
    | exact resolve eq73 eq22200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq22200
  have eq22530 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq22446
       have i₂ := eq22079
       grind)
    | exact superpose eq22079 eq22446
    | exact resolve eq22446 eq22079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22079 eq22446
  have eq22571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22530 eq15
    | exact resolve eq15 eq22530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22530
  have eq22619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq22571
    | exact resolve eq22571 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22571
  have eq22628 : False := by grind
  exact eq22628

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pyy_pyx_Equation335 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law335 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k (M.op X1 X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq9 X0 X0
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1)
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq66
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq84 X0
       grind)
    | exact resolve eq12 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq52 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq130 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq72
    | (have j0 := eq72 X2 X2
       grind)
    | exact resolve eq72 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq111 (σ x)
       have i₂ := eq72 x x
       grind)
    | exact superpose eq72 eq111
    | (have j0 := eq111 (σ X0)
       have j1 := eq72 X0 X0
       grind)
    | exact resolve eq111 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq143 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq72 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq72 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq72 X0 X1
       grind)
    | exact resolve eq12 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq146 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq145 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq147 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq150 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq140 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq153 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq147 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq147 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq154 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq150 X0
       have j1 := eq146 X0
       grind)
    | (have r₁ := eq150 X0
       have r₂ := eq146 X0
       grind)
    | exact resolve eq150 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq150
  have eq159 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq154 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq154
    | (have j0 := eq154 X0
       grind)
    | exact resolve eq154 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq323 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq153 (M.op X0 X0) X1
       have i₂ := eq106 X0 (M.op X0 X0)
       grind)
    | exact superpose eq106 eq153
    | (have j0 := eq153 (M.op X0 X0) X1
       grind)
    | exact resolve eq153 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 X1
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq323
    | (have j0 := eq323 X0 X1
       grind)
    | exact resolve eq323 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq323
  have eq333 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq332 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq351 : ∀ X0 X1 : G, (k (τ X1) (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (M.op X0 X0)
       have i₂ := eq333 X0 X1
       grind)
    | exact superpose eq333 eq23
    | exact resolve eq23 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq357 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq333 X0 (σ X1)
       grind)
    | exact superpose eq333 eq15
    | exact resolve eq15 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq370 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 X1
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq357
    | exact resolve eq357 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq375 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ X1)) = (τ (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1
       have i₂ := eq106 X0 (τ X1)
       grind)
    | exact superpose eq106 eq351
    | exact resolve eq351 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq351
  have eq469 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ (M.op X0 X0))
       have i₂ := eq370 X0 X1
       grind)
    | exact superpose eq370 eq9
    | exact resolve eq9 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 X1
       have i₂ := eq370 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq370 eq469
    | exact resolve eq469 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq469
  have eq494 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq489 X0 X1
       have i₂ := eq9 X1 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq489
    | exact resolve eq489 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq545 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (τ (M.op (σ (M.op X1 X1)) X0))) = (τ (M.op X0 (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq375 X1 (M.op (σ (M.op X1 X1)) X0)
       have i₂ := eq9 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq9 eq375
    | exact resolve eq375 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 : G, (τ (M.op X0 (σ (M.op X1 X1)))) = (M.op (M.op X1 X1) (M.op (M.op X1 X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 X1
       have i₂ := eq375 X1 X0
       grind)
    | exact superpose eq375 eq545
    | exact resolve eq545 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq545
  have eq562 : ∀ X0 X1 : G, (τ (M.op X0 (σ (M.op X1 X1)))) = (M.op (τ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq557 X0 X1
       have i₂ := eq9 (τ X0) (M.op X1 X1)
       grind)
    | exact superpose eq9 eq557
    | exact resolve eq557 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq3668 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq130 X0 (τ X0) (τ X0)
       have i₂ := eq159 (τ X0)
       grind)
    | exact superpose eq159 eq130
    | (have j0 := eq130 X0 (τ X0) (τ X0)
       have j1 := eq159 (τ X0)
       grind)
    | exact resolve eq130 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq3669 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq159 (τ X0)
       grind)
    | exact superpose eq159 eq19
    | (have j1 := eq159 (τ X0)
       grind)
    | exact resolve eq19 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq3718 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq3668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668
  have eq3744 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3669 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3669
    | (have j0 := eq3669 X0
       grind)
    | exact resolve eq3669 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3669
  have eq3745 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op X0 (k X0 X0)) ∨ (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3718 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3718
    | (have j0 := eq3718 X0
       grind)
    | exact resolve eq3718 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3718
  have eq3758 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3744 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3744
    | (have j0 := eq3744 X0
       grind)
    | exact resolve eq3744 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3744
  have eq3759 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3745 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3745
    | (have j0 := eq3745 X0
       grind)
    | exact resolve eq3745 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3745
  have eq3770 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3758 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3758
    | (have j0 := eq3758 X0
       grind)
    | exact resolve eq3758 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3758
  have eq3771 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3759 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3759
    | (have j0 := eq3759 X0
       grind)
    | exact resolve eq3759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3759
  have eq3777 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3771 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3771
    | (have j0 := eq3771 X0
       grind)
    | exact resolve eq3771 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771
  have eq3778 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq3777 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq3782 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3778 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3778
    | (have j0 := eq3778 X0
       grind)
    | exact resolve eq3778 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778
  have eq3889 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (k X0 X0) X0
       have i₂ := eq3782 X0
       grind)
    | exact superpose eq3782 eq13
    | (have j0 := eq13 (k X0 X0) X0
       have j1 := eq3782 X0
       grind)
    | (have r₁ := eq13 (k X0 X0) X0
       have r₂ := eq3782 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq3782 X0
       grind)
    | exact resolve eq13 eq3782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782
  have eq3900 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3889 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq3901 : ∀ X0 : G, (M.op X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3900 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3900
  have eq4026 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3770 X0
       have i₂ := eq3901 X0
       grind)
    | exact superpose eq3901 eq3770
    | (have j0 := eq3770 X0
       have j1 := eq3901 X0
       grind)
    | exact resolve eq3770 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770 eq3901
  have eq4051 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4026
  have eq4063 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4051 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4051 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq4051 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4051
  have eq4106 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 X1
       have i₂ := eq4063 X0
       grind)
    | exact superpose eq4063 eq153
    | (have j0 := eq153 X0 X1
       grind)
    | exact resolve eq153 eq4063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq4128 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4063 (σ X0)
       grind)
    | exact superpose eq4063 eq15
    | exact resolve eq15 eq4063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4157 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4128 X0
       have i₂ := eq4063 X0
       grind)
    | exact superpose eq4063 eq4128
    | exact resolve eq4128 eq4063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4063 eq4128
  have eq20806 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4157 X0
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq4157
    | (have j1 := eq77 X0 X1
       grind)
    | exact resolve eq4157 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq533329 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq20806 X1 X0
       grind)
    | exact superpose eq20806 eq11
    | (have j1 := eq20806 X1 X0
       grind)
    | exact resolve eq11 eq20806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20806
  have eq533588 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq533329 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq533329
    | (have j0 := eq533329 X0 X1
       grind)
    | exact resolve eq533329 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq533329
  have eq533874 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq533588 X0 X1
       have j1 := eq4106 X1 X0
       grind)
    | (have r₁ := eq533588 X0 X0
       have r₂ := eq4106 X0 X1
       grind)
    | exact resolve eq533588 eq4106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106 eq533588
  have eq534376 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq533874 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq533874
    | exact resolve eq533874 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534837 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq533874 (σ X1) X0
       grind)
    | exact superpose eq533874 eq15
    | (have j1 := eq533874 (σ X1) X0
       grind)
    | exact resolve eq15 eq533874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533874
  have eq538087 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq534376 (τ X0) X1
       grind)
    | exact superpose eq534376 eq19
    | (have j1 := eq534376 (τ X0) X1
       grind)
    | exact resolve eq19 eq534376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq534376
  have eq543113 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq538087 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq538087
    | exact resolve eq538087 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538087
  have eq544158 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq543113 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq543113
    | (have j0 := eq543113 X0 X1
       grind)
    | exact resolve eq543113 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543113
  have eq553024 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq534837 x y
       grind)
    | exact superpose eq534837 eq16
    | (have j1 := eq534837 x y
       grind)
    | exact resolve eq16 eq534837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534837
  have eq562812 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq553024
       have i₂ := eq544158 x y
       grind)
    | exact superpose eq544158 eq553024
    | (have j1 := eq544158 (σ x) (σ y)
       grind)
    | (have r₁ := eq553024
       have r₂ := eq544158 x y
       grind)
    | exact resolve eq553024 eq544158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544158 eq553024
  have eq562815 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq562812
  have eq564639 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq562815
       grind)
    | exact superpose eq562815 eq9
    | exact resolve eq9 eq562815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564710 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq564639
       grind)
    | exact superpose eq564639 eq9
    | exact resolve eq9 eq564639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564639
  have eq568554 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq564710
       have i₂ := eq562815
       grind)
    | exact superpose eq562815 eq564710
    | exact resolve eq564710 eq562815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562815 eq564710
  have eq568608 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq568554
  have eq568666 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq568608
       grind)
    | exact superpose eq568608 eq9
    | exact resolve eq9 eq568608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568671 : (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq67 (σ y) (σ x)
       have i₂ := eq568608
       grind)
    | exact superpose eq568608 eq67
    | exact resolve eq67 eq568608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq568722 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq568671
       have i₂ := eq4157 y
       grind)
    | exact superpose eq4157 eq568671
    | exact resolve eq568671 eq4157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4157 eq568671
  have eq609972 : (τ (σ y)) = (M.op (τ (M.op (σ y) (σ x))) (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq562 (M.op (σ y) (σ x)) y
       have i₂ := eq568722
       grind)
    | exact superpose eq568722 eq562
    | exact resolve eq562 eq568722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq568722
  have eq610056 : y = (M.op (τ (M.op (σ y) (σ x))) (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq609972
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq609972
    | exact resolve eq609972 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609972
  have eq610874 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq610056
       have i₂ := eq568666
       grind)
    | exact superpose eq568666 eq610056
    | exact resolve eq610056 eq568666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568666 eq610056
  have eq610956 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq610874
  have eq611081 : y = (M.op (τ (σ y)) (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq610956
       have i₂ := eq568608
       grind)
    | exact superpose eq568608 eq610956
    | exact resolve eq610956 eq568608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568608 eq610956
  have eq611161 : y = (M.op (τ (σ y)) (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq611081
  have eq611191 : y = (M.op y (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq611161
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq611161
    | exact resolve eq611161 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611161
  have eq611218 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq611191
       have i₂ := eq9 y y
       grind)
    | exact superpose eq9 eq611191
    | exact resolve eq611191 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611191
  have eq611219 : y = (M.op y y) := by grind
  clear eq611218
  have eq611944 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq494 y x
       have i₂ := eq611219
       grind)
    | exact superpose eq611219 eq494
    | exact resolve eq494 eq611219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq611219
  have eq623662 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq611944 x
       grind)
    | exact superpose eq611944 eq16
    | (have r₁ := eq16
       have r₂ := eq611944 x
       grind)
    | exact resolve eq16 eq611944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611944
  have eq624135 : False := by grind
  exact eq624135

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq62 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq93 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq95 (σ X0) (σ X1)
       grind)
    | exact superpose eq95 eq15
    | (have j1 := eq95 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq95 (τ X0) X1
       grind)
    | exact superpose eq95 eq18
    | (have j1 := eq95 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq95
  have eq104 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq100 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq122 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq104
    | (have j0 := eq104 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq377 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98 x y
       grind)
    | exact superpose eq98 eq16
    | (have j1 := eq98 x y
       grind)
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq391 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq377
       have i₂ := eq122 x y
       grind)
    | exact superpose eq122 eq377
    | (have j1 := eq122 (σ x) (σ y)
       grind)
    | (have r₁ := eq377
       have r₂ := eq122 x y
       grind)
    | (have r₁ := eq377
       have r₂ := eq122 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq377
       have r₂ := eq122 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq377 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq377
  have eq392 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq391
  have eq394 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq392
       grind)
    | exact superpose eq392 eq16
    | exact resolve eq16 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq630 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq64 (M.op X0 X0) X1
       grind)
    | exact superpose eq64 eq9
    | (have j1 := eq64 (M.op X0 X0) X1
       grind)
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq12415 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op X0 X0))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq630 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq630 eq62
    | (have j1 := eq630 X0 x
       grind)
    | exact resolve eq62 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq630
  have eq12453 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12415 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq12415
    | (have j0 := eq12415 X0
       grind)
    | exact resolve eq12415 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12415
  have eq12458 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12453 X0
       have j1 := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | (have r₁ := eq12453 X0
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12453 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12453
  have eq12460 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq12458
  have eq12478 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12460
  have eq12561 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq12478 (σ X0)
       grind)
    | exact superpose eq12478 eq15
    | exact resolve eq15 eq12478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12607 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12561 X0
       have i₂ := eq12478 X0
       grind)
    | exact superpose eq12478 eq12561
    | exact resolve eq12561 eq12478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12478 eq12561
  have eq12818 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq394
       have i₂ := eq12607 x
       grind)
    | exact superpose eq12607 eq394
    | (have r₁ := eq394
       have r₂ := eq12607 x
       grind)
    | exact resolve eq394 eq12607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq12835 : (σ x) = (σ y) := by grind
  clear eq12818
  have eq12873 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12835
       grind)
    | exact superpose eq12835 eq16
    | exact resolve eq16 eq12835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12874 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12835
       grind)
    | exact superpose eq12835 eq10
    | exact resolve eq10 eq12835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12835
  have eq12947 : x = y := by
    first
    | (have i₁ := eq12874
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12874
    | exact resolve eq12874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12874
  have eq12948 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12873
       have i₂ := eq12607 x
       grind)
    | exact superpose eq12607 eq12873
    | exact resolve eq12873 eq12607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12607 eq12873
  have eq12952 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12948
       have i₂ := eq12947
       grind)
    | exact superpose eq12947 eq12948
    | exact resolve eq12948 eq12947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12947 eq12948
  have eq12953 : False := by grind
  exact eq12953

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_pyy_pxy_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq213 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq217 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq238 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq213 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq293 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq236 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq294 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq294 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq294
    | (have j0 := eq294 (σ X0)
       grind)
    | exact resolve eq294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq314 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq298 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq324 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq314 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq314
    | (have j0 := eq314 (τ X0)
       grind)
    | exact resolve eq314 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq324 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq324
    | (have j0 := eq324 X0
       grind)
    | exact resolve eq324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq327 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq326 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq326
    | (have j0 := eq326 X0
       grind)
    | exact resolve eq326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq328 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq327 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq327
    | (have j0 := eq327 X0
       grind)
    | exact resolve eq327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq334 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq328 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq328
    | (have j0 := eq328 (τ X0)
       grind)
    | exact resolve eq328 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq433 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq238 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq434 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq454 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq434 X0 (σ X1)
       grind)
    | exact superpose eq434 eq22
    | (have j1 := eq434 X0 X1
       grind)
    | exact resolve eq22 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq455 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq434 X0 (τ X1)
       grind)
    | exact superpose eq434 eq18
    | (have j1 := eq434 X0 X1
       grind)
    | exact resolve eq18 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq467 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq434 X0 X1
       grind)
    | exact superpose eq434 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq434 X2 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq434 X0 X1
       grind)
    | exact resolve eq12 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq467 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq573 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq472 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq574 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq573 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq576 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq574 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq574
    | exact resolve eq574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq574 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq574
    | exact resolve eq574 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq334 X0
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq334
    | (have j0 := eq334 X0
       grind)
    | exact resolve eq334 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq580 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq314 X0
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq314
    | (have j0 := eq314 X0
       grind)
    | exact resolve eq314 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq585 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq577 X0
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq577
    | exact resolve eq577 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq586 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq576 X0
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq576
    | exact resolve eq576 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq576
  have eq604 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq585 X0
       grind)
    | exact superpose eq585 eq9
    | exact resolve eq9 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq585 X0
       grind)
    | exact superpose eq585 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq586 X0
       grind)
    | exact superpose eq586 eq9
    | exact resolve eq9 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq586 X0
       grind)
    | exact superpose eq586 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq454
    | (have j0 := eq454 X1 X1
       grind)
    | exact resolve eq454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq694 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq740 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq455 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq455
    | (have j0 := eq455 X1 X1
       grind)
    | exact resolve eq455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq790 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq740 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq740
    | (have j0 := eq740 X0 X1
       grind)
    | exact resolve eq740 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq858 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0
       have i₂ := eq434 X0 X1
       grind)
    | exact superpose eq434 eq580
    | (have j0 := eq580 X0
       have j1 := eq434 X0 X1
       grind)
    | exact resolve eq580 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq869 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq858 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq881 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq869 X0 X1
       have i₂ := eq586 X0
       grind)
    | exact superpose eq586 eq869
    | (have j0 := eq869 X0 X1
       grind)
    | exact resolve eq869 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq892 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq881 (τ X0) X1
       have i₂ := eq585 X0
       grind)
    | exact superpose eq585 eq881
    | (have j0 := eq881 (τ X0) X1
       grind)
    | exact resolve eq881 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq946 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq892 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq892
    | (have j0 := eq892 X0 X1
       grind)
    | exact resolve eq892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq947 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq946 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq946
    | (have j0 := eq946 X0 X1
       grind)
    | exact resolve eq946 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq958 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq947 X1 (τ X0)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq947
    | (have j0 := eq947 X1 X1
       grind)
    | exact resolve eq947 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq947 X0 X1
       grind)
    | exact superpose eq947 eq17
    | (have j1 := eq947 X0 X1
       grind)
    | exact resolve eq17 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq947
  have eq986 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0
       have i₂ := eq434 X0 X1
       grind)
    | exact superpose eq434 eq578
    | (have j0 := eq578 X0
       have j1 := eq434 X0 X1
       grind)
    | exact resolve eq578 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq578
  have eq999 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq986 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1011 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq999 X0 X1
       have i₂ := eq585 X0
       grind)
    | exact superpose eq585 eq999
    | (have j0 := eq999 X0 X1
       grind)
    | exact resolve eq999 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq999
  have eq1075 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1011 (σ X0) X1
       have i₂ := eq586 X0
       grind)
    | exact superpose eq586 eq1011
    | (have j0 := eq1011 (σ X0) X1
       grind)
    | exact resolve eq1011 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq1011
  have eq1111 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1075 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1075
    | (have j0 := eq1075 X0 X1
       grind)
    | exact resolve eq1075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1116 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1111 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1111
    | (have j0 := eq1111 X0 X1
       grind)
    | exact resolve eq1111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1124 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1116 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1116
    | (have j0 := eq1116 X0 X1
       grind)
    | exact resolve eq1116 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1340 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1124 x y
       grind)
    | exact superpose eq1124 eq16
    | (have j1 := eq1124 x x
       grind)
    | exact resolve eq16 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1372 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1340
       have i₂ := eq790 y x
       grind)
    | exact superpose eq790 eq1340
    | (have j1 := eq790 x x
       grind)
    | (have r₁ := eq1340
       have r₂ := eq790 y x
       grind)
    | exact resolve eq1340 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq1340
  have eq1373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq1372
  have eq1374 : x = (M.op x x) := by grind
  clear eq1373
  have eq1384 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0
       have i₂ := eq1374
       grind)
    | exact superpose eq1374 eq9
    | exact resolve eq9 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1385 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq1374
       grind)
    | exact superpose eq1374 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq1374
       grind)
    | exact resolve eq12 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1390 : ∀ X0 : G, (M.op (τ x) X0) = (M.op X0 (M.op X0 (τ x))) := by
    intro X0
    first
    | (have i₁ := eq604 x X0
       have i₂ := eq1374
       grind)
    | exact superpose eq1374 eq604
    | exact resolve eq604 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq1391 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq628 x X0
       have i₂ := eq1374
       grind)
    | exact superpose eq1374 eq628
    | exact resolve eq628 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq1399 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1385 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq2698 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (M.op X0 (τ x)) = (k X0 (τ x)) := by
    intro X0
    first
    | (have i₁ := eq605 x X0
       have i₂ := eq1374
       grind)
    | exact superpose eq1374 eq605
    | (have j0 := eq605 x X0
       grind)
    | exact resolve eq605 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq2701 : ∀ X0 : G, (M.op X0 (τ x)) = (k X0 (τ x)) := by
    intro X0
    first
    | (have j0 := eq2698 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698
  have eq2724 : ∀ X0 : G, (τ (k X0 x)) = (M.op (τ X0) (τ x)) := by
    intro X0
    first
    | (have i₁ := eq2701 (τ X0)
       have i₂ := eq29 x X0
       grind)
    | exact superpose eq29 eq2701
    | exact resolve eq2701 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2701
  have eq2740 : ∀ X0 : G, (τ (M.op X0 x)) = (M.op (τ X0) (τ x)) := by
    intro X0
    first
    | (have i₁ := eq2724 X0
       have i₂ := eq1399 X0
       grind)
    | exact superpose eq1399 eq2724
    | exact resolve eq2724 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724
  have eq2819 : ∀ X0 : G, (M.op (τ x) (τ X0)) = (M.op (τ X0) (τ (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq1390 (τ X0)
       have i₂ := eq2740 X0
       grind)
    | exact superpose eq2740 eq1390
    | exact resolve eq1390 eq2740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390 eq2740
  have eq2911 : ∀ X0 : G, (M.op (τ x) (τ X0)) = (τ (k X0 (M.op X0 x))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq958 (M.op X0 x) X0
       have i₂ := eq2819 X0
       grind)
    | exact superpose eq2819 eq958
    | (have j0 := eq958 X0 X0
       grind)
    | exact resolve eq958 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq2912 : ∀ X0 : G, (σ (M.op (τ x) (τ X0))) = (k X0 (σ (τ (M.op X0 x)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq968 X0 (τ (M.op X0 x))
       have i₂ := eq2819 X0
       grind)
    | exact superpose eq2819 eq968
    | (have j0 := eq968 X0 x
       grind)
    | exact resolve eq968 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq2819
  have eq2916 : ∀ X0 : G, (σ (M.op (τ x) (τ X0))) = (k X0 (M.op X0 x)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2912 X0
       have i₂ := eq11 (M.op X0 x)
       grind)
    | exact superpose eq11 eq2912
    | (have j0 := eq2912 X0
       grind)
    | exact resolve eq2912 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2912
  have eq3385 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq629 x X0
       have i₂ := eq1374
       grind)
    | exact superpose eq1374 eq629
    | (have j0 := eq629 x X0
       grind)
    | exact resolve eq629 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq3388 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq3385 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385
  have eq3412 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3388 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq3388
    | exact resolve eq3388 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388
  have eq3438 : ∀ X0 : G, (σ (M.op X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3412 X0
       have i₂ := eq1399 X0
       grind)
    | exact superpose eq1399 eq3412
    | exact resolve eq3412 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399 eq3412
  have eq3487 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ X0) (σ (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq1391 (σ X0)
       have i₂ := eq3438 X0
       grind)
    | exact superpose eq3438 eq1391
    | exact resolve eq1391 eq3438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391 eq3438
  have eq3623 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 (M.op X0 x))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1124 X0 (M.op X0 x)
       have i₂ := eq3487 X0
       grind)
    | exact superpose eq3487 eq1124
    | (have j0 := eq1124 X0 x
       grind)
    | exact resolve eq1124 eq3487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124 eq3487
  have eq41365 : ∀ X0 : G, (M.op (τ x) (τ X0)) = (τ (M.op X0 (M.op X0 x))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq694 (M.op X0 x) X0
       have i₂ := eq2911 X0
       grind)
    | exact superpose eq2911 eq694
    | (have j0 := eq694 X0 X0
       have j1 := eq2911 X0
       grind)
    | exact resolve eq694 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq2911
  have eq41442 : ∀ X0 : G, (M.op (τ x) (τ X0)) = (τ (M.op X0 (M.op X0 x))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq41365 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41365
  have eq41449 : ∀ X0 : G, (M.op (τ x) (τ X0)) = (τ (M.op x X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq41442 X0
       have i₂ := eq1384 X0
       grind)
    | exact superpose eq1384 eq41442
    | (have j0 := eq41442 X0
       grind)
    | exact resolve eq41442 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384 eq41442
  have eq41615 : ∀ X0 : G, (k X0 (M.op X0 x)) = (σ (τ (M.op x X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2916 X0
       have i₂ := eq41449 X0
       grind)
    | exact superpose eq41449 eq2916
    | (have j0 := eq2916 X0
       have j1 := eq41449 X0
       grind)
    | exact resolve eq2916 eq41449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916 eq41449
  have eq41906 : ∀ X0 : G, (k X0 (M.op X0 x)) = (σ (τ (M.op x X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq41615 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41615
  have eq42035 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op X0 x)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq41906 X0
       have i₂ := eq11 (M.op x X0)
       grind)
    | exact superpose eq11 eq41906
    | (have j0 := eq41906 X0
       grind)
    | exact resolve eq41906 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41906
  have eq42546 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3623 X0
       have i₂ := eq42035 X0
       grind)
    | exact superpose eq42035 eq3623
    | (have j0 := eq3623 X0
       have j1 := eq42035 X0
       grind)
    | exact resolve eq3623 eq42035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623 eq42035
  have eq42757 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq42546 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42546
  have eq42853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42757 y
       grind)
    | exact superpose eq42757 eq16
    | (have j1 := eq42757 y
       grind)
    | (have r₁ := eq16
       have r₂ := eq42757 y
       grind)
    | exact resolve eq16 eq42757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42757
  have eq42906 : y = (M.op y y) := by grind
  clear eq42853
  have eq42912 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq42906
       grind)
    | exact superpose eq42906 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq42906
       grind)
    | exact resolve eq12 eq42906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42921 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq629 y X0
       have i₂ := eq42906
       grind)
    | exact superpose eq42906 eq629
    | (have j0 := eq629 y X0
       grind)
    | exact resolve eq629 eq42906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629 eq42906
  have eq42931 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq42921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42921
  have eq42936 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq42912 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42912
  have eq43063 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq42931 (σ X0)
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq42931
    | exact resolve eq42931 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42931
  have eq43118 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq43063 X0
       have i₂ := eq42936 X0
       grind)
    | exact superpose eq42936 eq43063
    | exact resolve eq43063 eq42936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42936 eq43063
  have eq44542 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43118 x
       grind)
    | exact superpose eq43118 eq16
    | (have r₁ := eq16
       have r₂ := eq43118 x
       grind)
    | exact resolve eq16 eq43118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43118
  have eq44555 : False := by grind
  exact eq44555

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_y_pxy_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq55 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 x
       grind)
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq66 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq287 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq55
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq14 sF3 sF3
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq304
  have eq306 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq299
  have eq3295 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq287 (τ X0) X1
       grind)
    | exact superpose eq287 eq49
    | (have j1 := eq287 (τ X0) (τ X0)
       grind)
    | exact resolve eq49 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq287
  have eq3360 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3295 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3295
    | (have j0 := eq3295 X0 (τ X0)
       grind)
    | exact resolve eq3295 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295
  have eq3402 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3360 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq3360 X0 X1
       have r₂ := eq12 X0 (σ (τ X0))
       grind)
    | (have r₁ := eq3360 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq3360 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360
  have eq3437 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3402 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3402
    | (have j0 := eq3402 X0 X1
       grind)
    | exact resolve eq3402 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3402
  have eq3462 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3437 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3437
    | (have j0 := eq3437 X1 X1
       grind)
    | exact resolve eq3437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3437
  have eq3697 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq3462 sF3 sF2
       grind)
    | exact superpose eq3462 eq61
    | (have j1 := eq3462 x (σ x)
       grind)
    | exact resolve eq61 eq3462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3699 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq3697
    | exact resolve eq3697 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3697
  have eq3701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3699
       have i₂ := eq3462 y x
       grind)
    | exact superpose eq3462 eq3699
    | (have j1 := eq3462 x (σ x)
       grind)
    | exact resolve eq3699 eq3462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3699
  have eq3722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3701
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3701
    | exact resolve eq3701 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3701
  have eq3726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3722
    | exact resolve eq3722 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3722
  have eq3728 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq3726
       have r₂ := eq27
       grind)
    | exact resolve eq3726 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3726
  have eq3734 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3728 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq3728
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq3728
       grind)
    | exact resolve eq12 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3736 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq3734 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3734
  have eq3755 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3736 eq55
    | exact resolve eq55 eq3736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq3736
  have eq3833 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq3755
       grind)
    | exact superpose eq3755 eq10
    | exact resolve eq10 eq3755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3755
  have eq3897 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3728 eq3833
    | exact resolve eq3833 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728 eq3833
  have eq3922 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq3897
  have eq3924 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq3922
    | exact resolve eq3922 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3922
  have eq3931 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq3924
       grind)
    | exact superpose eq3924 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3924
  have eq3933 : x = (M.op x x) := by grind
  clear eq3931
  have eq3944 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq3933
       grind)
    | exact superpose eq3933 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq3933
       grind)
    | exact resolve eq12 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3945 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0
       have i₂ := eq3933
       grind)
    | exact superpose eq3933 eq9
    | exact resolve eq9 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3946 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3944 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3944
  have eq3948 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq3946 X0
       grind)
    | exact superpose eq3946 eq30
    | exact resolve eq30 eq3946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq4169 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq306
       have i₂ := eq3946 x
       grind)
    | exact superpose eq3946 eq306
    | exact resolve eq306 eq3946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq3946
  have eq4238 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4169
       have i₂ := eq3933
       grind)
    | exact superpose eq3933 eq4169
    | exact resolve eq4169 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3933 eq4169
  have eq4326 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4238
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4238
    | exact resolve eq4238 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4238
  have eq4327 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4326
  have eq4362 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq4327 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq4327
       grind)
    | exact resolve eq12 eq4327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4363 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq4327 eq9
    | exact resolve eq9 eq4327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4327
  have eq4364 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq4362 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4362
  have eq4436 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq4364 eq3948
    | exact resolve eq3948 eq4364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948 eq4364
  have eq4587 : ∀ X0 : G, (k (σ y) (M.op (σ X0) (σ x))) = (σ (k y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 x)
       have i₂ := eq4436 X0
       grind)
    | exact superpose eq4436 eq36
    | exact resolve eq36 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4436
  have eq6818 : (k (σ y) (M.op (σ y) (σ x))) = (σ (k y (M.op y x))) := by
    first
    | (have i₁ := eq4587 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4587
    | (have j0 := eq4587 y
       grind)
    | exact resolve eq4587 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq6880 : (M.op (σ y) (M.op (σ y) (σ x))) = (σ (k y (M.op y x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6818 eq3462
    | (have j0 := eq3462 x (σ y)
       grind)
    | exact resolve eq3462 eq6818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6818
  have eq6887 : (M.op (σ x) (σ y)) = (σ (k y (M.op y x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4363 eq6880
    | exact resolve eq6880 eq4363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363 eq6880
  have eq6894 : (M.op (σ x) (σ y)) = (σ (k y (M.op y x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq6887
    | exact resolve eq6887 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6887
  have eq8525 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6894
       have i₂ := eq3462 (M.op y x) y
       grind)
    | exact superpose eq3462 eq6894
    | (have j1 := eq3462 x (σ y)
       grind)
    | exact resolve eq6894 eq3462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462 eq6894
  have eq8555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8525
       have i₂ := eq3945 y
       grind)
    | exact superpose eq3945 eq8525
    | exact resolve eq8525 eq3945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3945 eq8525
  have eq8559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8555
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8555
    | exact resolve eq8555 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8555
  have eq8563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq8559
    | exact resolve eq8559 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8559
  have eq8565 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq8563
       have r₂ := eq27
       grind)
    | exact resolve eq8563 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8563
  have eq9058 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq8565 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq8565
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq8565
       grind)
    | exact resolve eq12 eq8565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9068 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq9058 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9058
  have eq9103 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq9068 eq66
    | exact resolve eq66 eq9068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq9068
  have eq12065 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq9103
       grind)
    | exact superpose eq9103 eq10
    | exact resolve eq10 eq9103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9103
  have eq12618 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8565 eq12065
    | exact resolve eq12065 eq8565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8565 eq12065
  have eq12648 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq12618
  have eq12650 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq39 eq12648
    | exact resolve eq12648 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq12648
  have eq12666 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq12650
       grind)
    | exact superpose eq12650 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq12650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12650
  have eq12668 : y = (M.op y y) := by grind
  clear eq12666
  have eq12724 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq12668
       grind)
    | exact superpose eq12668 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq12668
       grind)
    | exact resolve eq12 eq12668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12734 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq12724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12724
  have eq13105 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq12734 x
       grind)
    | exact superpose eq12734 eq61
    | exact resolve eq61 eq12734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq13180 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq305
       have i₂ := eq12734 y
       grind)
    | exact superpose eq12734 eq305
    | exact resolve eq305 eq12734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq12734
  have eq13537 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13180
       have i₂ := eq12668
       grind)
    | exact superpose eq12668 eq13180
    | exact resolve eq13180 eq12668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12668 eq13180
  have eq13592 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13105
    | exact resolve eq13105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq13105
  have eq13905 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13537
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13537
    | exact resolve eq13537 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13537
  have eq13906 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq13905
  have eq13944 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13592
    | exact resolve eq13592 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13592
  have eq14059 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq13906 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq13906
       grind)
    | exact resolve eq12 eq13906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13906
  have eq14069 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq14059 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14059
  have eq14271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14069 eq13944
    | exact resolve eq13944 eq14069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13944 eq14069
  have eq14361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14271
    | exact resolve eq14271 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14271
  have eq14597 : False := by grind
  exact eq14597

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_pxx_pyx_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq291 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq291 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq304 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq300 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq300 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq300 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq363 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq304 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq364 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq364 (σ X0)
       grind)
    | exact superpose eq364 eq15
    | exact resolve eq15 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq376 X0
       have i₂ := eq364 X0
       grind)
    | exact superpose eq364 eq376
    | exact resolve eq376 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq376
  have eq439 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq395 X0
       grind)
    | exact superpose eq395 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq395 X0
       grind)
    | exact superpose eq395 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq395 X0
       grind)
    | exact superpose eq395 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq395 X0
       grind)
    | exact superpose eq395 eq9
    | exact resolve eq9 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq444 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq440 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq440 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq440 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq445 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq439 X0 X1
       have j1 := eq442 X0 X1
       grind)
    | (have r₁ := eq439 X0 X1
       have r₂ := eq442 X0 X1
       grind)
    | exact resolve eq439 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq496 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq445 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq445
    | (have j0 := eq445 X0 X1
       grind)
    | exact resolve eq445 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq562 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq496 (τ X0) X1
       grind)
    | exact superpose eq496 eq18
    | (have j1 := eq496 X0 X1
       grind)
    | exact resolve eq18 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq496
  have eq827 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq562 (σ X0) X1
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
  have eq893 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq827
    | (have j0 := eq827 X0 X1
       grind)
    | exact resolve eq827 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq1084 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq444 X0 X1
       grind)
    | exact superpose eq444 eq10
    | (have j1 := eq444 X0 X1
       grind)
    | exact resolve eq10 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq1145 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1084 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1084
    | (have j0 := eq1084 X0 X1
       grind)
    | exact resolve eq1084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1182 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1145 X1 (σ X0)
       grind)
    | exact superpose eq1145 eq15
    | (have j1 := eq1145 X1 X1
       grind)
    | exact resolve eq15 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1344 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1182 x y
       grind)
    | exact superpose eq1182 eq16
    | (have j1 := eq1182 x y
       grind)
    | exact resolve eq16 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1410 : y = (M.op y y) := by
    first
    | (have j1 := eq893 x y
       grind)
    | (have r₁ := eq1344
       have r₂ := eq893 x y
       grind)
    | exact resolve eq1344 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq1344
  have eq1440 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq1410
       grind)
    | exact superpose eq1410 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq1410
       grind)
    | exact resolve eq12 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1442 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq442 y X0
       have i₂ := eq1410
       grind)
    | exact superpose eq1410 eq442
    | (have j0 := eq442 y X0
       grind)
    | exact resolve eq442 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq1410
  have eq1448 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq1442 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442
  have eq1450 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq1440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq1471 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1448 (σ X0)
       grind)
    | exact superpose eq1448 eq15
    | exact resolve eq15 eq1448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1491 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1471 X0
       have i₂ := eq1450 X0
       grind)
    | exact superpose eq1450 eq1471
    | exact resolve eq1471 eq1450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450 eq1471
  have eq1647 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (M.op (σ y) (σ (M.op y (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq443 X0 (σ y)
       have i₂ := eq1491 (M.op X0 X0)
       grind)
    | exact superpose eq1491 eq443
    | exact resolve eq443 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq1670 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op y (M.op y (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1647 X0
       have i₂ := eq1491 (M.op y (M.op X0 X0))
       grind)
    | exact superpose eq1491 eq1647
    | exact resolve eq1647 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491 eq1647
  have eq1679 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1670 X0
       have i₂ := eq9 X0 y
       grind)
    | exact superpose eq9 eq1670
    | exact resolve eq1670 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq1755 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1679 x
       grind)
    | exact superpose eq1679 eq16
    | (have r₁ := eq16
       have r₂ := eq1679 x
       grind)
    | exact resolve eq16 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679
  have eq1774 : False := by grind
  exact eq1774
