import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq80 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq78
  have eq100 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq101 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq121
    | exact resolve eq121 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq101
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq16
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq123
  have eq148 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq190 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq738 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ x) X0 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq5022 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq148 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq148
    | (have j0 := eq148 x
       grind)
    | exact resolve eq148 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq5050 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5022
  have eq5055 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5050
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5050
    | exact resolve eq5050 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5050
  have eq5071 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5055
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq5055 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5055
  have eq5080 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5071 eq50
    | exact resolve eq50 eq5071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq5272 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq190 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq190
    | (have j0 := eq190 y
       grind)
    | exact resolve eq190 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq5298 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5272
  have eq5300 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5298
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq5298
    | exact resolve eq5298 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5298
  have eq5323 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5300
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq5300 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5300
  have eq5346 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5323 eq129
    | exact resolve eq129 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq12950 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5071 eq80
    | exact resolve eq80 eq5071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq13867 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5323 eq130
    | exact resolve eq130 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq17996 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq12950
       grind)
    | exact superpose eq12950 eq16
    | exact resolve eq16 eq12950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12950
  have eq18049 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5080 eq17996
    | exact resolve eq17996 eq5080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17996
  have eq18053 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq18049
       have r₂ := eq13 x x
       grind)
    | exact resolve eq18049 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18049
  have eq18054 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq18053
       grind)
    | exact superpose eq18053 eq44
    | exact resolve eq44 eq18053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq18087 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq5071 eq18054
    | exact resolve eq18054 eq5071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5071 eq18054
  have eq18719 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq13867
       grind)
    | exact superpose eq13867 eq16
    | exact resolve eq16 eq13867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13867
  have eq18776 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5346 eq18719
    | exact resolve eq18719 eq5346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18719
  have eq18780 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq18776
       have r₂ := eq13 x y
       grind)
    | exact resolve eq18776 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18776
  have eq18781 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18780
       grind)
    | exact superpose eq18780 eq101
    | exact resolve eq101 eq18780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq18814 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq5323 eq18781
    | exact resolve eq18781 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5323 eq18781
  have eq25687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq25688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq25687
    | exact resolve eq25687 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25687
  have eq25699 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq25688
       have r₂ := eq28
       grind)
    | exact resolve eq25688 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25688
  have eq25704 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq25699 eq5346
    | exact resolve eq5346 eq25699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5346 eq25699
  have eq25758 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25704
       have i₂ := eq18780
       grind)
    | exact superpose eq18780 eq25704
    | exact resolve eq25704 eq18780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18780 eq25704
  have eq25766 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq25758
    | exact resolve eq25758 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25758
  have eq25767 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq25766
  have eq25773 : (τ (σ x)) = (k x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq25767 eq5080
    | exact resolve eq5080 eq25767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5080 eq25767
  have eq25851 : (τ (σ x)) = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25773
       have i₂ := eq18053
       grind)
    | exact superpose eq18053 eq25773
    | exact resolve eq25773 eq18053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18053 eq25773
  have eq25861 : x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq25851
    | exact resolve eq25851 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25851
  have eq25862 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq25861
  have eq25872 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18814
       have i₂ := eq25862
       grind)
    | exact superpose eq25862 eq18814
    | exact resolve eq18814 eq25862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18814
  have eq25882 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq55 y y
       have i₂ := eq25862
       grind)
    | exact superpose eq25862 eq55
    | exact resolve eq55 eq25862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25862
  have eq25915 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25882
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25882
    | exact resolve eq25882 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25882
  have eq25918 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25872
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25872
    | exact resolve eq25872 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25872
  have eq25964 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq738 x
       have i₂ := eq25915
       grind)
    | exact superpose eq25915 eq738
    | exact resolve eq738 eq25915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq25915
  have eq26026 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56 eq25964
    | exact resolve eq25964 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq25964
  have eq26036 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26026
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26026
    | exact resolve eq26026 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq26026
  have eq26037 : y = (M.op x y) := by grind
  clear eq26036
  have eq26041 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26037 eq21
    | exact resolve eq21 eq26037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq26037
  have eq26219 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26041
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26041
    | exact resolve eq26041 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq26041
  have eq26781 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq26219 eq27
    | exact resolve eq27 eq26219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq26837 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq26219 eq742
    | exact resolve eq742 eq26219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq30414 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26219 eq25918
    | exact resolve eq25918 eq26219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25918 eq26219
  have eq30428 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30414 eq55
    | exact resolve eq55 eq30414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq30414
  have eq30471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26781 eq30428
    | exact resolve eq30428 eq26781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30428
  have eq30480 : x = (M.op x x) := by
    first
    | (have r₁ := eq30471
       have r₂ := eq28
       grind)
    | exact resolve eq30471 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30471
  have eq30508 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18087
       have i₂ := eq30480
       grind)
    | exact superpose eq30480 eq18087
    | exact resolve eq18087 eq30480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18087 eq30480
  have eq30582 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq30508
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30508
    | exact resolve eq30508 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq30508
  have eq30912 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq30582 eq26837
    | exact resolve eq26837 eq30582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26837 eq30582
  have eq30969 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq57 eq30912
    | exact resolve eq30912 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq30912
  have eq30985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26781 eq30969
    | exact resolve eq30969 eq26781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26781 eq30969
  have eq30999 : False := by grind
  exact eq30999

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X1) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq41
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq41 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq21
    | exact resolve eq21 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq68
    | exact resolve eq68 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq175 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq181 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq180 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq3751 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ (τ X2))) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (k X0 (τ X1))
       have i₂ := eq162 X0 X1 (τ X2)
       grind)
    | exact superpose eq162 eq17
    | (have j1 := eq162 X0 X1 (τ X2)
       grind)
    | exact resolve eq17 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq162
  have eq3789 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) X2) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3751 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq3751
    | (have j0 := eq3751 X0 X1 X2
       grind)
    | exact resolve eq3751 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3751
  have eq3814 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3789 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq3789
    | (have j0 := eq3789 X0 X1 X2
       grind)
    | exact resolve eq3789 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789
  have eq3834 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3814 X0 X1 X2
       have j1 := eq12 X2 (k (σ X0) X1)
       grind)
    | (have r₁ := eq3814 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X0) X1)
       grind)
    | exact resolve eq3814 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814
  have eq3852 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) ∨ (M.op X2 (k (σ X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3834 X0 X1 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3834
    | (have j0 := eq3834 X0 X1 X2
       grind)
    | exact resolve eq3834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834
  have eq5738 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op (k X0 X2) X1) ∨ (M.op X1 (k X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3852 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3852
    | exact resolve eq3852 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5758 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) X2) = (k X2 (σ (k X0 X1))) ∨ (M.op X2 (σ (k X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3852 X0 (σ X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3852
    | exact resolve eq3852 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3852
  have eq6160 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq69 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq6161 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq6160 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6160
  have eq6164 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6161 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6161
    | (have j0 := eq6161 X0
       grind)
    | exact resolve eq6161 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6161
  have eq6189 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6164 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6164
    | exact resolve eq6164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6164
  have eq6262 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6189 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq6189
    | (have j0 := eq6189 X0
       grind)
    | exact resolve eq6189 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6189
  have eq6279 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq6262 X0
       grind)
    | exact superpose eq6262 eq11
    | (have j1 := eq6262 X0
       grind)
    | exact resolve eq11 eq6262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6262
  have eq6376 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6279 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq6279
    | (have j0 := eq6279 X0
       grind)
    | exact resolve eq6279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6279
  have eq6382 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6376 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq6376 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq6376 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6376
  have eq6650 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq6382 X0
       grind)
    | exact superpose eq6382 eq181
    | (have j0 := eq181 X0 X1
       grind)
    | exact resolve eq181 eq6382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq6663 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) ∨ (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5738 X0 X1 X0
       have i₂ := eq6382 X0
       grind)
    | exact superpose eq6382 eq5738
    | exact resolve eq5738 eq6382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5738
  have eq6690 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6382 (σ X0)
       grind)
    | exact superpose eq6382 eq15
    | exact resolve eq15 eq6382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6698 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0 X0
       have i₂ := eq6382 (τ X0)
       grind)
    | exact superpose eq6382 eq47
    | exact resolve eq47 eq6382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq6752 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6698 X0
       have i₂ := eq6382 X0
       grind)
    | exact superpose eq6382 eq6698
    | exact resolve eq6698 eq6382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6698
  have eq6758 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6690 X0
       have i₂ := eq6382 X0
       grind)
    | exact superpose eq6382 eq6690
    | exact resolve eq6690 eq6382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6382 eq6690
  have eq6955 : ∀ X0 X1 : G, (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) = (M.op X1 (M.op (M.op (τ X0) X1) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (τ X0) (τ X0)
       have i₂ := eq6752 X0
       grind)
    | exact superpose eq6752 eq97
    | exact resolve eq97 eq6752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6752
  have eq7343 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0) (σ X0)
       have i₂ := eq6758 X0
       grind)
    | exact superpose eq6758 eq21
    | exact resolve eq21 eq6758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7345 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (σ X0) (σ X0)
       have i₂ := eq6758 X0
       grind)
    | exact superpose eq6758 eq23
    | exact resolve eq23 eq6758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7353 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) = (M.op X1 (M.op (M.op (σ X0) X1) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0) (σ X0)
       have i₂ := eq6758 X0
       grind)
    | exact superpose eq6758 eq97
    | exact resolve eq97 eq6758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24273 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (k X1 (σ (M.op X0 X0))) ∨ (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6663 (σ X0) X1
       have i₂ := eq6758 X0
       grind)
    | exact superpose eq6758 eq6663
    | exact resolve eq6663 eq6758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6663 eq6758
  have eq141769 : ∀ X0 X1 : G, (k (τ X1) (M.op X0 X0)) = (τ (M.op (σ (M.op X0 X0)) X1)) ∨ (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (M.op X0 X0)
       have i₂ := eq24273 X0 X1
       grind)
    | exact superpose eq24273 eq35
    | (have j1 := eq24273 X0 X1
       grind)
    | exact resolve eq35 eq24273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq24273
  have eq281662 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq141769 X0 (σ X0)
       have i₂ := eq7343 X0
       grind)
    | exact superpose eq7343 eq141769
    | (have j0 := eq141769 X0 (σ X0)
       grind)
    | exact resolve eq141769 eq7343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7343 eq141769
  have eq282141 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq281662 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq281662
    | (have j0 := eq281662 X0
       grind)
    | exact resolve eq281662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281662
  have eq282266 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282141 X0
       have i₂ := eq7345 X0
       grind)
    | exact superpose eq7345 eq282141
    | (have j0 := eq282141 X0
       grind)
    | exact resolve eq282141 eq7345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7345 eq282141
  have eq282385 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5758 X0 (M.op X0 X0) x
       have i₂ := eq282266 X0
       grind)
    | exact superpose eq282266 eq5758
    | (have j1 := eq282266 X0
       grind)
    | exact resolve eq5758 eq282266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5758 eq282266
  have eq282633 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq282385 X0 X1
       have j1 := eq6650 X0 X1
       grind)
    | (have r₁ := eq282385 X0 X1
       have r₂ := eq6650 X0 X1
       grind)
    | exact resolve eq282385 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6650 eq282385
  have eq289541 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq282633 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq282633
    | exact resolve eq282633 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289841 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq282633 X0 (σ X1)
       grind)
    | exact superpose eq282633 eq15
    | (have j1 := eq282633 X0 (σ X1)
       grind)
    | exact resolve eq15 eq282633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282633
  have eq290386 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq289541 (τ X0) X1
       grind)
    | exact superpose eq289541 eq18
    | (have j1 := eq289541 (τ X0) X1
       grind)
    | exact resolve eq18 eq289541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq289541
  have eq304263 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq290386 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq290386
    | exact resolve eq290386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290386
  have eq304982 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq304263 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq304263
    | (have j0 := eq304263 X0 X1
       grind)
    | exact resolve eq304263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304263
  have eq409872 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq289841 x y
       grind)
    | exact superpose eq289841 eq16
    | (have j1 := eq289841 x y
       grind)
    | exact resolve eq16 eq289841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289841
  have eq411744 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq409872
       have i₂ := eq304982 x y
       grind)
    | exact superpose eq304982 eq409872
    | (have j1 := eq304982 (σ x) (σ y)
       grind)
    | (have r₁ := eq409872
       have r₂ := eq304982 x y
       grind)
    | exact resolve eq409872 eq304982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304982 eq409872
  have eq411751 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq411744
  have eq412944 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq23 y x
       have i₂ := eq411751
       grind)
    | exact superpose eq411751 eq23
    | exact resolve eq23 eq411751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq411751
  have eq413421 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq25 (σ y) (σ x) X0
       have i₂ := eq412944
       grind)
    | exact superpose eq412944 eq25
    | exact resolve eq25 eq412944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq412944
  have eq413797 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq413421 X0
       have i₂ := eq21 (σ y) X0
       grind)
    | exact superpose eq21 eq413421
    | exact resolve eq413421 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413421
  have eq416873 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 y y
       have i₂ := eq413797 X0
       grind)
    | exact superpose eq413797 eq97
    | (have j1 := eq413797 X1
       grind)
    | exact resolve eq97 eq413797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq413797
  have eq417123 : ∀ X0 X1 : G, (M.op (σ y) X1) = X1 ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq416873 X1 X1
       have i₂ := eq21 y X1
       grind)
    | exact superpose eq21 eq416873
    | (have j0 := eq416873 X0 X1
       grind)
    | exact resolve eq416873 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416873
  have eq417555 : ∀ X0 X1 : G, (M.op (M.op (τ (σ y)) X0) (τ (σ y))) = (M.op X0 (M.op (M.op (τ (σ y)) X0) (τ (σ y)))) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq6955 (σ y) X1
       have i₂ := eq417123 X0 (σ y)
       grind)
    | exact superpose eq417123 eq6955
    | (have j1 := eq417123 X1 X1
       grind)
    | exact resolve eq6955 eq417123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6955 eq417123
  have eq418275 : ∀ X0 X1 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq417555 X1 X1
       have i₂ := eq21 (τ (σ y)) X1
       grind)
    | exact superpose eq21 eq417555
    | (have j0 := eq417555 X0 X1
       grind)
    | exact resolve eq417555 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417555
  have eq418445 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq418275 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq418275
    | (have j0 := eq418275 X0 X0
       grind)
    | exact resolve eq418275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418275
  have eq424720 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq418445 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418445
  have eq424721 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq424720 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424720
  have eq424789 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7353 y x
       have i₂ := eq424721 y
       grind)
    | exact superpose eq424721 eq7353
    | exact resolve eq7353 eq424721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7353
  have eq425942 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq424789 x
       have i₂ := eq21 (σ y) x
       grind)
    | exact superpose eq21 eq424789
    | exact resolve eq424789 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq424789
  have eq444952 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq425942 (σ x)
       grind)
    | exact superpose eq425942 eq16
    | exact resolve eq16 eq425942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425942
  have eq445207 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq444952
       have i₂ := eq424721 x
       grind)
    | exact superpose eq424721 eq444952
    | exact resolve eq444952 eq424721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424721 eq444952
  have eq445208 : False := by grind
  exact eq445208

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq40 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq35
    | exact resolve eq35 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq69 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq41
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq41 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq35
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq35 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq21
    | exact resolve eq21 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X0 ∨ (k (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2)) X0) = X0 ∨ (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2)) ≠ X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2)) X0
       have i₂ := eq19 X1 X2 X3 X0
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2)) X0
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X2)) X0
       have i₂ := eq19 X1 X2 X3 X0
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq136 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (k X1 (σ X2)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (k X1 (σ X2))
       have i₂ := eq33 X1 X2 X0
       grind)
    | exact superpose eq33 eq14
    | (have j0 := eq14 (σ X0) (k X1 (σ X2))
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq202 : ∀ X0 X1 X2 : G, (σ (k (k X1 (τ X0)) X2)) = (k (M.op X0 (σ X1)) (σ X2)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X1 X0 X2
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq234 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1) (σ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq21
    | (have j1 := eq68 X1 X0
       grind)
    | exact resolve eq21 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq242 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq241 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq244 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq239 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq245 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq244 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq244 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq244 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq253 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq242 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq242
    | (have j0 := eq242 (τ X0)
       grind)
    | exact resolve eq242 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq255 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq253 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq253
    | (have j0 := eq253 X0
       grind)
    | exact resolve eq253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq258 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq255 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq255
    | (have j0 := eq255 X0
       grind)
    | exact resolve eq255 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq270 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq245 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq245
    | (have j0 := eq245 (τ X0) X1
       grind)
    | exact resolve eq245 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq275 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq272
    | (have j0 := eq272 X0 X1
       grind)
    | exact resolve eq272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq281 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq275 (τ X0) X1
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq275
    | (have j0 := eq275 (τ X0) X1
       grind)
    | exact resolve eq275 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq710 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (σ (k (M.op X1 (τ X0)) X2)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op X1 (τ X0)) X2
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq15
    | (have j1 := eq70 X1 X0
       grind)
    | exact resolve eq15 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq731 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (σ (k (M.op X1 (τ X0)) X2)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq710 X0 X1 X2
       have i₂ := eq34 X0 X1 X2
       grind)
    | exact superpose eq34 eq710
    | (have j0 := eq710 X0 X1 X2
       grind)
    | exact resolve eq710 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq710
  have eq1082 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (τ X0) X1)) X0) ∨ (M.op (τ X0) X1) = (M.op (M.op (τ X0) X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (M.op (τ X0) X1)
       have i₂ := eq23 (τ X0) X1
       grind)
    | exact superpose eq23 eq71
    | (have j0 := eq71 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq71 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (τ X0) X1)) X0) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1082 X0 X1
       have i₂ := eq21 (τ X0) X1
       grind)
    | exact superpose eq21 eq1082
    | (have j0 := eq1082 X0 X1
       grind)
    | exact resolve eq1082 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq2005 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq234 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq234
    | (have j0 := eq234 (τ X0) (τ X1)
       grind)
    | exact resolve eq234 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq2068 : ∀ X0 X1 : G, (M.op (σ (τ (k X0 X1))) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2005 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2005
    | (have j0 := eq2005 X0 X1
       grind)
    | exact resolve eq2005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2070 : ∀ X0 X1 : G, (M.op (k X0 X1) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2068 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2068
    | (have j0 := eq2068 X0 X1
       grind)
    | exact resolve eq2068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2072 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op (k X0 X1) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2070 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2070
    | (have j0 := eq2070 X0 X1
       grind)
    | exact resolve eq2070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq2073 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (k X0 X1) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2072 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2072
    | (have j0 := eq2072 X0 X1
       grind)
    | exact resolve eq2072 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq2074 : ∀ X0 X1 : G, (M.op (k X0 X1) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2073 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2073
    | (have j0 := eq2073 X0 X1
       grind)
    | exact resolve eq2073 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073
  have eq2082 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op (M.op (M.op X0 X2) (k X1 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (k X1 X0) X0
       have i₂ := eq2074 X1 X0
       grind)
    | exact superpose eq2074 eq9
    | (have j1 := eq2074 X0 X0
       grind)
    | exact resolve eq9 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074
  have eq2551 : ∀ X0 X1 X2 X3 X4 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k (M.op (M.op X2 X0) (M.op (M.op (M.op X3 X4) X2) X3)) X0) = X0 ∨ (M.op (M.op X2 X0) (M.op (M.op (M.op X3 X4) X2) X3)) ≠ X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq121 X0 X2 X3 X4
       grind)
    | exact superpose eq121 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq121 X0 X2 X3 X4
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq121 X0 X1 X2 X3
       grind)
    | exact resolve eq12 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2624 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (k X1 X0) ∨ (k (M.op (M.op X2 X0) (M.op (M.op (M.op X3 X4) X2) X3)) X0) = X0 ∨ (M.op (M.op X2 X0) (M.op (M.op (M.op X3 X4) X2) X3)) ≠ X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq2551 X0 X1 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551
  have eq5145 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69
    | (have j0 := eq69 X1 X1
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq5250 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5145 X0 X1
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq5145
    | (have j0 := eq5145 X0 X1
       grind)
    | exact resolve eq5145 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5145
  have eq6920 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2082 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082
  have eq6921 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6920 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6920
  have eq7010 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97 X0 X0 X0
       have i₂ := eq6921 X0 X1
       grind)
    | exact superpose eq6921 eq97
    | (have j1 := eq6921 X0 X2
       grind)
    | exact resolve eq97 eq6921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6921
  have eq7100 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7010 X0 X1 X2
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq7010
    | (have j0 := eq7010 X0 X1 X2
       grind)
    | exact resolve eq7010 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7010
  have eq7245 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7100 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7100
  have eq7246 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7245
  have eq7369 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq7246 X0
       grind)
    | exact superpose eq7246 eq9
    | exact resolve eq9 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7371 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 (k X0 X0) X0 X0
       have i₂ := eq7246 X0
       grind)
    | exact superpose eq7246 eq22
    | exact resolve eq22 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7246
  have eq7469 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7371 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq7371
    | exact resolve eq7371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7470 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7371 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq7371
    | exact resolve eq7371 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7847 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (k (σ X0) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0 (k (σ X0) (σ X0))
       have i₂ := eq7369 (σ X0)
       grind)
    | exact superpose eq7369 eq72
    | (have j0 := eq72 X0 (k (σ X0) (σ X0))
       grind)
    | exact resolve eq72 eq7369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq7848 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (k (τ X0) (τ X0)) = (M.op (k (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (k (τ X0) (τ X0))
       have i₂ := eq7369 (τ X0)
       grind)
    | exact superpose eq7369 eq71
    | (have j0 := eq71 X0 (k (τ X0) (τ X0))
       grind)
    | exact resolve eq71 eq7369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq7369
  have eq7850 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (k (τ X0) (τ X0)) = (M.op (k (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7848 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq7848
    | (have j0 := eq7848 X0
       grind)
    | exact resolve eq7848 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7848
  have eq7851 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (k (σ X0) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7847 x
       have i₂ := eq35 (σ x) x
       grind)
    | exact superpose eq35 eq7847
    | (have j0 := eq7847 X0
       grind)
    | exact resolve eq7847 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7847
  have eq7852 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k (τ X0) (τ X0)) = (M.op (k (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7850 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7850
    | (have j0 := eq7850 X0
       grind)
    | exact resolve eq7850 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7850
  have eq7853 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k (σ X0) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7851 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7851
    | (have j0 := eq7851 X0
       grind)
    | exact resolve eq7851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7851
  have eq7854 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7852 X0
       have i₂ := eq7371 (τ X0)
       grind)
    | exact superpose eq7371 eq7852
    | (have j0 := eq7852 X0
       grind)
    | exact resolve eq7852 eq7371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7852
  have eq7855 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7853 X0
       have i₂ := eq7371 (σ X0)
       grind)
    | exact superpose eq7371 eq7853
    | (have j0 := eq7853 X0
       grind)
    | exact resolve eq7853 eq7371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7371 eq7853
  have eq7856 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq7854 X0
       have j1 := eq258 (τ X0)
       grind)
    | (have r₁ := eq7854 X0
       have r₂ := eq258 (τ X0)
       grind)
    | exact resolve eq7854 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7854
  have eq7857 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq7855 X0
       have j1 := eq258 (σ X0)
       grind)
    | (have r₁ := eq7855 X0
       have r₂ := eq258 (σ X0)
       grind)
    | exact resolve eq7855 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq7855
  have eq7900 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (k X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (k X0 X0)) (σ X0)
       have i₂ := eq7469 X0
       grind)
    | exact superpose eq7469 eq9
    | exact resolve eq9 eq7469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8239 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7470 X0
       have i₂ := eq5250 X0 X0
       grind)
    | exact superpose eq5250 eq7470
    | (have j1 := eq5250 X0 X0
       grind)
    | exact resolve eq7470 eq5250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5250
  have eq8262 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (k X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (τ (k X0 X0)) (τ X0) X1
       have i₂ := eq7470 X0
       grind)
    | exact superpose eq7470 eq25
    | exact resolve eq25 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8317 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8239 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8239
  have eq13650 : ∀ X0 : G, (M.op (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8317 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8317
    | (have j0 := eq8317 (σ X0)
       grind)
    | exact resolve eq8317 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8317
  have eq14489 : ∀ X0 X1 : G, (τ (σ (M.op (τ (σ X0)) X1))) = (k (τ (σ (M.op (τ (σ X0)) X1))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (σ (M.op (τ (σ X0)) X1)) X0
       have i₂ := eq1117 (σ X0) X1
       grind)
    | exact superpose eq1117 eq35
    | (have j1 := eq1117 (σ X0) X1
       grind)
    | exact resolve eq35 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq14515 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (k (M.op (τ (σ X0)) X1) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14489 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq14489
    | (have j0 := eq14489 X0 X1
       grind)
    | exact resolve eq14489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14489
  have eq14547 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14515 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14515
    | (have j0 := eq14515 X0 X1
       grind)
    | exact resolve eq14515 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14515
  have eq14567 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14547 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14547
    | (have j0 := eq14547 X0 X1
       grind)
    | exact resolve eq14547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14547
  have eq14584 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14567 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14567
    | (have j0 := eq14567 X0 X1
       grind)
    | exact resolve eq14567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14567
  have eq17652 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (k (σ X0) (σ X0)) X0
       have i₂ := eq7856 (σ X0)
       grind)
    | exact superpose eq7856 eq35
    | (have j1 := eq7856 (σ X0)
       grind)
    | exact resolve eq35 eq7856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17653 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq7856 (τ X0)
       grind)
    | exact superpose eq7856 eq18
    | (have j1 := eq7856 (τ X0)
       grind)
    | exact resolve eq18 eq7856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7856
  have eq17700 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17653 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq17653
    | (have j0 := eq17653 X0
       grind)
    | exact resolve eq17653 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17653
  have eq17701 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq17652 x
       have i₂ := eq35 (σ x) x
       grind)
    | exact superpose eq35 eq17652
    | (have j0 := eq17652 X0
       grind)
    | exact resolve eq17652 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17652
  have eq17745 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17700 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17700
    | (have j0 := eq17700 X0
       grind)
    | exact resolve eq17700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17700
  have eq17746 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq17701 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17701
    | (have j0 := eq17701 X0
       grind)
    | exact resolve eq17701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17701
  have eq17785 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17746 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17746
    | (have j0 := eq17746 X0
       grind)
    | exact resolve eq17746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17746
  have eq17835 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq731 X0 (τ X0) (τ X0)
       have i₂ := eq17785 (τ X0)
       grind)
    | exact superpose eq17785 eq731
    | (have j0 := eq731 X0 (τ X0) x
       have j1 := eq17785 (τ X0)
       grind)
    | exact resolve eq731 eq17785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq17785
  have eq17895 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq17835 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17835
  have eq17937 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17895 X0
       have i₂ := eq18 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq17895
    | (have j0 := eq17895 X0
       grind)
    | exact resolve eq17895 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17895
  have eq17980 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17937 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq17937
    | (have j0 := eq17937 X0
       grind)
    | exact resolve eq17937 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17937
  have eq18013 : ∀ X0 : G, (k X0 X0) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17980 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17980
    | (have j0 := eq17980 X0
       grind)
    | exact resolve eq17980 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17980
  have eq18688 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7857 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq7857
    | (have j0 := eq7857 (τ X0)
       grind)
    | exact resolve eq7857 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7857
  have eq18800 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18688 X0
       have i₂ := eq47 X0 (k X0 X0)
       grind)
    | exact superpose eq47 eq18688
    | (have j0 := eq18688 X0
       grind)
    | exact resolve eq18688 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18688
  have eq18842 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18800 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18800
    | (have j0 := eq18800 X0
       grind)
    | exact resolve eq18800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18800
  have eq19094 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18842 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq18842
    | (have j0 := eq18842 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq18842 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18842
  have eq19199 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19094
  have eq19292 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (τ (σ (k (k X0 (τ (σ X0))) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19199 (σ X0)
       have i₂ := eq202 (σ X0) X0 X0
       grind)
    | exact superpose eq202 eq19199
    | (have j0 := eq19199 (σ X0)
       have j1 := eq202 (σ X0) X0 x
       grind)
    | exact resolve eq19199 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq19199
  have eq19385 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (τ (σ (k (k X0 (τ (σ X0))) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq19292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19292
  have eq19441 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (k X0 (τ (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19385 X0
       have i₂ := eq10 (k (k X0 (τ (σ X0))) X0)
       grind)
    | exact superpose eq10 eq19385
    | (have j0 := eq19385 X0
       grind)
    | exact resolve eq19385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19385
  have eq19444 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19441 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19441
    | (have j0 := eq19441 X0
       grind)
    | exact resolve eq19441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19441
  have eq57399 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X2))) ≠ X1 ∨ (k (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X2)) X1) = X1 ∨ (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X2)) ≠ X1 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq2624 X1 X1 X0 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2624
  have eq57401 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X2)) ≠ X1 ∨ (k (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X2)) X1) = X1 ∨ (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X2)) ≠ X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57399 X0 X1 X2 X3
       have i₂ := eq122 X1 X0 X2 X3
       grind)
    | exact superpose eq122 eq57399
    | (have j0 := eq57399 X0 X1 X2 X3
       grind)
    | exact resolve eq57399 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq57399
  have eq57402 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X2)) ≠ X1 ∨ (k (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X2)) X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq57401 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57401
  have eq63262 : ∀ X0 X1 X2 : G, (k X2 (σ (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ (τ X2))) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (k (τ X0) X1)
       have i₂ := eq136 (τ X2) X0 X1
       grind)
    | exact superpose eq136 eq17
    | (have j1 := eq136 (τ X2) X0 X1
       grind)
    | exact resolve eq17 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq63386 : ∀ X0 X1 X2 : G, (k X2 (σ (k (τ X0) X1))) = (M.op (k X0 (σ X1)) X2) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63262 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq63262
    | (have j0 := eq63262 X0 X1 X2
       grind)
    | exact resolve eq63262 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63262
  have eq63477 : ∀ X0 X1 X2 : G, (k X2 (k X0 (σ X1))) = (M.op (k X0 (σ X1)) X2) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63386 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq63386
    | (have j0 := eq63386 X0 X1 X2
       grind)
    | exact resolve eq63386 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63386
  have eq63526 : ∀ X0 X1 X2 : G, (k X2 (k X0 (σ X1))) = (M.op (k X0 (σ X1)) X2) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63477 X0 X1 X2
       have j1 := eq12 X2 (k X0 (σ X1))
       grind)
    | (have r₁ := eq63477 X0 X1 X2
       have r₂ := eq12 X0 (k X0 (σ X1))
       grind)
    | exact resolve eq63477 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63477
  have eq63568 : ∀ X0 X1 X2 : G, (k X2 (k X0 (σ X1))) = (M.op (k X0 (σ X1)) X2) ∨ (M.op X2 (k X0 (σ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63526 X0 X1 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63526
    | (have j0 := eq63526 X0 X1 X2
       grind)
    | exact resolve eq63526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63526
  have eq124201 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (τ (τ (σ X0))) = (M.op (τ (τ (σ X0))) (τ (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17745 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq17745
    | (have j0 := eq17745 (σ X0)
       grind)
    | exact resolve eq17745 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17745
  have eq124355 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ (τ (σ X0))) = (M.op (τ (τ (σ X0))) (τ (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq124201 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq124201
    | (have j0 := eq124201 X0
       grind)
    | exact resolve eq124201 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124201
  have eq124408 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq124355 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq124355
    | (have j0 := eq124355 X0
       grind)
    | exact resolve eq124355 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124355
  have eq125579 : ∀ X0 : G, (σ (σ (k X0 X0))) = (σ (k (σ (k X0 X0)) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq124408 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq124408
    | (have j0 := eq124408 (σ X0)
       grind)
    | exact resolve eq124408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124408
  have eq125812 : ∀ X0 : G, (σ (σ (k X0 X0))) = (σ (σ (k (k X0 X0) X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq125579 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq125579
    | (have j0 := eq125579 X0
       grind)
    | exact resolve eq125579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125579
  have eq125837 : ∀ X0 : G, (σ (σ (k X0 X0))) = (σ (σ (k (k X0 X0) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq125812 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq125812
    | (have j0 := eq125812 X0
       grind)
    | exact resolve eq125812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125812
  have eq125861 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq125837 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq125837
    | (have j0 := eq125837 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq125837 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125837
  have eq126059 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq125861 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125861
  have eq139756 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq18013 (σ X0)
       grind)
    | exact superpose eq18013 eq35
    | (have j1 := eq18013 (σ X0)
       grind)
    | exact resolve eq35 eq18013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18013
  have eq139849 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq139756 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq139756
    | (have j0 := eq139756 X0
       grind)
    | exact resolve eq139756 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139756
  have eq139904 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (k (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq139849 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139849
    | (have j0 := eq139849 X0
       grind)
    | exact resolve eq139849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139849
  have eq139932 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (τ (σ X0)) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq139904 X0
       have i₂ := eq35 (σ X0) X0
       grind)
    | exact superpose eq35 eq139904
    | (have j0 := eq139904 X0
       grind)
    | exact resolve eq139904 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139904
  have eq139949 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k X0 X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq139932 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139932
    | (have j0 := eq139932 X0
       grind)
    | exact resolve eq139932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139932
  have eq139961 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq139949 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139949
    | (have j0 := eq139949 X0
       grind)
    | exact resolve eq139949 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139949
  have eq142333 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14584 X0 X0
       have i₂ := eq139961 X0
       grind)
    | exact superpose eq139961 eq14584
    | (have j0 := eq14584 X0 X0
       have j1 := eq139961 X0
       grind)
    | exact resolve eq14584 eq139961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14584 eq139961
  have eq142416 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq142333 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142333
  have eq142478 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq142416 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq142416 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq142416 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142416
  have eq142594 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq245 X0 X1
       have i₂ := eq142478 X0
       grind)
    | exact superpose eq142478 eq245
    | (have j0 := eq245 X0 X1
       grind)
    | exact resolve eq245 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq142600 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq142478 X0
       grind)
    | exact superpose eq142478 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq142637 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7469 X0
       have i₂ := eq142478 X0
       grind)
    | exact superpose eq142478 eq7469
    | exact resolve eq7469 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7469
  have eq142638 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7470 X0
       have i₂ := eq142478 X0
       grind)
    | exact superpose eq142478 eq7470
    | exact resolve eq7470 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7470
  have eq142651 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7900 X0 X1
       have i₂ := eq142478 X0
       grind)
    | exact superpose eq142478 eq7900
    | exact resolve eq7900 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7900
  have eq142660 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8262 X0 X1
       have i₂ := eq142478 X0
       grind)
    | exact superpose eq142478 eq8262
    | exact resolve eq8262 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8262
  have eq142884 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq142478 (σ X0)
       grind)
    | exact superpose eq142478 eq15
    | exact resolve eq15 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142898 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0 X0
       have i₂ := eq142478 (τ X0)
       grind)
    | exact superpose eq142478 eq47
    | exact resolve eq47 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142995 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq142898 X0
       have i₂ := eq142478 X0
       grind)
    | exact superpose eq142478 eq142898
    | exact resolve eq142898 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142898
  have eq143007 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq142884 X0
       have i₂ := eq142478 X0
       grind)
    | exact superpose eq142478 eq142884
    | exact resolve eq142884 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142884
  have eq144749 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq142637 X0
       grind)
    | exact superpose eq142637 eq97
    | exact resolve eq97 eq142637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142637
  have eq145294 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) = (M.op X1 (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq142638 X0
       grind)
    | exact superpose eq142638 eq97
    | exact resolve eq97 eq142638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142638
  have eq147727 : ∀ X0 : G, (σ (σ (τ (M.op X0 X0)))) = (σ (σ (k (τ (M.op X0 X0)) (τ X0)))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq126059 (τ X0)
       have i₂ := eq142995 X0
       grind)
    | exact superpose eq142995 eq126059
    | exact resolve eq126059 eq142995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126059
  have eq148088 : ∀ X0 : G, (σ (σ (τ (M.op X0 X0)))) = (σ (k (σ (τ (M.op X0 X0))) X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq147727 X0
       have i₂ := eq18 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq18 eq147727
    | (have j0 := eq147727 X0
       grind)
    | exact resolve eq147727 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq147727
  have eq148241 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq148088 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq148088
    | (have j0 := eq148088 X0
       grind)
    | exact resolve eq148088 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148088
  have eq241714 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq142600 X0 X1
       have i₂ := eq148241 X0
       grind)
    | exact superpose eq148241 eq142600
    | (have j0 := eq142600 X0 X1
       have j1 := eq148241 X0
       grind)
    | (have r₁ := eq142600 X0 X1
       have r₂ := eq148241 X0
       grind)
    | exact resolve eq142600 eq148241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142600 eq148241
  have eq241939 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq241714 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241714
  have eq305746 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) X2) = (k X2 (σ (k X0 X1))) ∨ (M.op X2 (σ (k X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63568 (σ X0) X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq63568
    | exact resolve eq63568 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305803 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ (σ X1)))) = (τ (M.op (k (σ X0) (σ X1)) X2)) ∨ (M.op X2 (k (σ X0) (σ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 (σ X1) X2
       have i₂ := eq63568 (σ X0) X1 X2
       grind)
    | exact superpose eq63568 eq49
    | (have j1 := eq63568 (σ X0) X1 X2
       grind)
    | exact resolve eq49 eq63568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq63568
  have eq306310 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ (σ X1)))) = (τ (M.op (σ (k X0 X1)) X2)) ∨ (M.op X2 (k (σ X0) (σ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305803 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq305803
    | (have j0 := eq305803 X0 X1 X2
       grind)
    | exact resolve eq305803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305803
  have eq306393 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (τ (M.op (σ (k X0 X1)) X2)) ∨ (M.op X2 (k (σ X0) (σ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq306310 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq306310
    | (have j0 := eq306310 X0 X1 X2
       grind)
    | exact resolve eq306310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306310
  have eq306450 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (τ (M.op (σ (k X0 X1)) X2)) ∨ (M.op X2 (σ (k X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq306393 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq306393
    | (have j0 := eq306393 X0 X1 X2
       grind)
    | exact resolve eq306393 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306393
  have eq385403 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13650 X0
       have i₂ := eq19444 X0
       grind)
    | exact superpose eq19444 eq13650
    | (have j0 := eq13650 X0
       have j1 := eq19444 X0
       grind)
    | exact resolve eq13650 eq19444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13650 eq19444
  have eq385884 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq385403 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385403
  have eq386300 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq385884 X0
       have i₂ := eq142478 X0
       grind)
    | exact superpose eq142478 eq385884
    | (have j0 := eq385884 X0
       grind)
    | exact resolve eq385884 eq142478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142478 eq385884
  have eq386742 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq386300 X0
       have i₂ := eq143007 X0
       grind)
    | exact superpose eq143007 eq386300
    | (have j0 := eq386300 X0
       grind)
    | exact resolve eq386300 eq143007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386300
  have eq389560 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq386742 X0
       grind)
    | exact superpose eq386742 eq10
    | (have j1 := eq386742 X0
       grind)
    | exact resolve eq10 eq386742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386742
  have eq389947 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq389560 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq389560
    | (have j0 := eq389560 X0
       grind)
    | exact resolve eq389560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389560
  have eq390036 : ∀ X0 : G, (τ X0) = (M.op (k (τ (M.op X0 X0)) (τ X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq389947 (τ X0)
       have i₂ := eq142995 X0
       grind)
    | exact superpose eq142995 eq389947
    | exact resolve eq389947 eq142995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389947
  have eq390465 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ (k (M.op X0 X0) X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq390036 X0
       have i₂ := eq47 X0 (M.op X0 X0)
       grind)
    | exact superpose eq47 eq390036
    | (have j0 := eq390036 X0
       grind)
    | exact resolve eq390036 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq390036
  have eq411324 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ X0)) X1) = X1 ∨ (τ X0) = (M.op (τ (k (M.op X0 X0) X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq142660 X0 X1
       have i₂ := eq390465 X0
       grind)
    | exact superpose eq390465 eq142660
    | (have j1 := eq390465 X0
       grind)
    | exact resolve eq142660 eq390465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142660 eq390465
  have eq411753 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (k (M.op X0 X0) X0)) (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq411324 X0 X1
       have i₂ := eq21 (τ X0) X1
       grind)
    | exact superpose eq21 eq411324
    | (have j0 := eq411324 X0 X1
       grind)
    | exact resolve eq411324 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411324
  have eq411935 : ∀ X0 X1 : G, (M.op (τ (k (M.op (σ X0) (σ X0)) (σ X0))) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq411753 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq411753
    | (have j0 := eq411753 (k (M.op (σ X0) (σ X0)) (σ X0)) X0
       grind)
    | exact resolve eq411753 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411753
  have eq412422 : ∀ X0 X1 : G, (M.op (k (τ (M.op (σ X0) (σ X0))) X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq411935 X0 X1
       have i₂ := eq35 (M.op (σ X0) (σ X0)) X0
       grind)
    | exact superpose eq35 eq411935
    | (have j0 := eq411935 (k (τ (M.op (σ X0) (σ X0))) X0) X0
       grind)
    | exact resolve eq411935 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411935
  have eq412502 : ∀ X0 X1 : G, (M.op (k (τ (σ (M.op X0 X0))) X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq412422 X0 X1
       have i₂ := eq143007 X0
       grind)
    | exact superpose eq143007 eq412422
    | (have j0 := eq412422 (k (τ (σ (M.op X0 X0))) X0) X0
       grind)
    | exact resolve eq412422 eq143007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412422
  have eq412538 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq412502 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq412502
    | (have j0 := eq412502 (k (M.op X0 X0) X0) X0
       grind)
    | exact resolve eq412502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412502
  have eq414209 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X0 (k (M.op X0 X0) X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (k (M.op X0 X0) X0) X0
       have i₂ := eq412538 X0 X1
       grind)
    | exact superpose eq412538 eq21
    | (have j1 := eq412538 X0 (k (M.op X0 X0) X0)
       grind)
    | exact resolve eq21 eq412538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412538
  have eq418319 : ∀ X0 : G, (k (M.op X0 X0) X0) ≠ (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = (M.op X0 (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq414209 X0 (k (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414209
  have eq418320 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq418319 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418319
  have eq418547 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq418320 (σ X0)
       have i₂ := eq143007 X0
       grind)
    | exact superpose eq143007 eq418320
    | exact resolve eq418320 eq143007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418628 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0 (k (M.op X0 X0) X0)
       have i₂ := eq418320 X0
       grind)
    | exact superpose eq418320 eq21
    | exact resolve eq21 eq418320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418320
  have eq419365 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq418547 x
       have i₂ := eq15 (M.op x x) x
       grind)
    | exact superpose eq15 eq418547
    | exact resolve eq418547 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418547
  have eq420870 : ∀ X0 : G, (σ X0) = (M.op (k (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq418628 (σ X0)
       have i₂ := eq143007 X0
       grind)
    | exact superpose eq143007 eq418628
    | exact resolve eq418628 eq143007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418628
  have eq421324 : ∀ X0 : G, (σ X0) = (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq420870 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq420870
    | exact resolve eq420870 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420870
  have eq699711 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (M.op X0 X0) X0)
       have i₂ := eq241939 X0 X1
       grind)
    | exact superpose eq241939 eq10
    | (have j1 := eq241939 X0 X1
       grind)
    | exact resolve eq10 eq241939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241939
  have eq700224 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq699711 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq699711
    | (have j0 := eq699711 X0 X1
       grind)
    | exact resolve eq699711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699711
  have eq700696 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq700224 (σ X0) X1
       grind)
    | exact superpose eq700224 eq35
    | (have j1 := eq700224 (σ X0) X1
       grind)
    | exact resolve eq35 eq700224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq700224
  have eq700917 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ (σ (M.op X0 X0))) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq700696 X0 X1
       have i₂ := eq143007 X0
       grind)
    | exact superpose eq143007 eq700696
    | (have j0 := eq700696 X0 X1
       grind)
    | exact resolve eq700696 eq143007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700696
  have eq701040 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq700917 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq700917
    | (have j0 := eq700917 X0 X1
       grind)
    | exact resolve eq700917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700917
  have eq701133 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq701040 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq701040
    | (have j0 := eq701040 X0 X1
       grind)
    | exact resolve eq701040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701040
  have eq703519 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq701133 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701133
  have eq703529 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq703519 X0
       grind)
    | (have r₁ := eq703519 x
       have r₂ := eq23 x x
       grind)
    | exact resolve eq703519 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703519
  have eq703681 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq703529 X0
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq703529
    | exact resolve eq703529 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703529
  have eq777828 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) ≠ X2 ∨ (k (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57402 (M.op X2 X1) X1 X2 X2
       have i₂ := eq25 X2 X1 X2
       grind)
    | exact superpose eq25 eq57402
    | exact resolve eq57402 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57402
  have eq783490 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq777828 (σ X0) (σ X0) (σ (M.op X0 X0))
       have i₂ := eq142651 X0 (σ X0)
       grind)
    | exact superpose eq142651 eq777828
    | exact resolve eq777828 eq142651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142651 eq777828
  have eq783654 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq783490 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq783490
    | (have j0 := eq783490 X0
       grind)
    | exact resolve eq783490 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783490
  have eq1817139 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (k (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq306450 (M.op X0 X0) X0 (σ X0)
       have i₂ := eq421324 X0
       grind)
    | exact superpose eq421324 eq306450
    | (have j0 := eq306450 (M.op X0 X0) X0 (σ X0)
       grind)
    | exact resolve eq306450 eq421324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306450 eq421324
  have eq1818535 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq1817139 X0
       have i₂ := eq703681 X0
       grind)
    | exact superpose eq703681 eq1817139
    | (have j0 := eq1817139 X0
       grind)
    | exact resolve eq1817139 eq703681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817139
  have eq1818787 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq1818535 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1818535
    | (have j0 := eq1818535 X0
       grind)
    | exact resolve eq1818535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818535
  have eq1818915 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1818787 X0
       have i₂ := eq419365 X0
       grind)
    | exact superpose eq419365 eq1818787
    | (have j0 := eq1818787 X0
       grind)
    | exact resolve eq1818787 eq419365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419365 eq1818787
  have eq1819004 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1818915 X0
       have i₂ := eq703681 X0
       grind)
    | exact superpose eq703681 eq1818915
    | (have j0 := eq1818915 X0
       grind)
    | exact resolve eq1818915 eq703681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703681 eq1818915
  have eq1822621 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq305746 X0 (M.op X0 X0) x
       have i₂ := eq1819004 X0
       grind)
    | exact superpose eq1819004 eq305746
    | (have j1 := eq1819004 X0
       grind)
    | exact resolve eq305746 eq1819004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305746
  have eq1822715 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1819004 (τ X0)
       grind)
    | exact superpose eq1819004 eq17
    | (have j1 := eq1819004 (τ X0)
       grind)
    | exact resolve eq17 eq1819004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1819004
  have eq1823278 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1822715 X0
       have i₂ := eq142995 X0
       grind)
    | exact superpose eq142995 eq1822715
    | (have j0 := eq1822715 X0
       grind)
    | exact resolve eq1822715 eq142995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822715
  have eq1823334 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1822621 X0 X1
       have j1 := eq142594 X0 X1
       grind)
    | (have r₁ := eq1822621 X0 X1
       have r₂ := eq142594 X0 X1
       grind)
    | exact resolve eq1822621 eq142594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142594 eq1822621
  have eq1823637 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1823278 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1823278
    | (have j0 := eq1823278 X0
       grind)
    | exact resolve eq1823278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823278
  have eq1823967 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1823637 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1823637
    | (have j0 := eq1823637 X0
       grind)
    | exact resolve eq1823637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823637
  have eq1824279 : ∀ X0 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1823967 X0
       have i₂ := eq142995 X0
       grind)
    | exact superpose eq142995 eq1823967
    | (have j0 := eq1823967 X0
       grind)
    | exact resolve eq1823967 eq142995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142995 eq1823967
  have eq1824574 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1824279 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1824279
    | (have j0 := eq1824279 X0
       grind)
    | exact resolve eq1824279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824279
  have eq1824843 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1824574 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1824574
    | (have j0 := eq1824574 X0
       grind)
    | exact resolve eq1824574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824574
  have eq1825206 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1824843 (σ X0)
       have i₂ := eq143007 X0
       grind)
    | exact superpose eq143007 eq1824843
    | exact resolve eq1824843 eq143007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143007 eq1824843
  have eq1826077 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1825206 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq1825206
    | (have j0 := eq1825206 X0
       grind)
    | exact resolve eq1825206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825206
  have eq1841338 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1823334 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1823334
    | exact resolve eq1823334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1842429 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1823334 X0 (σ X1)
       grind)
    | exact superpose eq1823334 eq15
    | (have j1 := eq1823334 X0 (σ X1)
       grind)
    | exact resolve eq15 eq1823334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823334
  have eq1863806 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq783654 X0
       have i₂ := eq1826077 X0
       grind)
    | exact superpose eq1826077 eq783654
    | (have j1 := eq1826077 X0
       grind)
    | (have r₁ := eq783654 X0
       have r₂ := eq1826077 X0
       grind)
    | exact resolve eq783654 eq1826077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783654 eq1826077
  have eq1864290 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1863806 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863806
  have eq1864291 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1864290 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864290
  have eq1864859 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq1864291 X0
       grind)
    | exact superpose eq1864291 eq10
    | exact resolve eq10 eq1864291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1864861 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (k X0 (M.op X0 X0))
       have i₂ := eq1864291 X0
       grind)
    | exact superpose eq1864291 eq15
    | exact resolve eq15 eq1864291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864291
  have eq1865577 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (k X1 (k X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1864861 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1864861
    | exact resolve eq1864861 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864861
  have eq1865579 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1864859 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1864859
    | exact resolve eq1864859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864859
  have eq1879011 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op (k X0 (M.op X0 X0)) X1)) ∨ (M.op X1 (k X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1865577 X0 X1
       have i₂ := eq1841338 (k X0 (M.op X0 X0)) X1
       grind)
    | exact superpose eq1841338 eq1865577
    | (have j1 := eq1841338 (k X0 (M.op X0 X0)) X1
       grind)
    | exact resolve eq1865577 eq1841338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841338 eq1865577
  have eq1880889 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 (k X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1879011 X0 X1
       have i₂ := eq1865579 X0
       grind)
    | exact superpose eq1865579 eq1879011
    | (have j0 := eq1879011 X0 X1
       grind)
    | exact resolve eq1879011 eq1865579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879011
  have eq1881393 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1880889 X0 X1
       have i₂ := eq1865579 X0
       grind)
    | exact superpose eq1865579 eq1880889
    | (have j0 := eq1880889 X0 X1
       grind)
    | exact resolve eq1880889 eq1865579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865579 eq1880889
  have eq2011972 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1842429 x y
       grind)
    | exact superpose eq1842429 eq16
    | (have j1 := eq1842429 x y
       grind)
    | exact resolve eq16 eq1842429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842429
  have eq2018830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2011972
       have i₂ := eq1881393 x y
       grind)
    | exact superpose eq1881393 eq2011972
    | (have j1 := eq1881393 (σ x) (σ y)
       grind)
    | (have r₁ := eq2011972
       have r₂ := eq1881393 x y
       grind)
    | exact resolve eq2011972 eq1881393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881393 eq2011972
  have eq2018833 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq2018830
  have eq2018847 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq23 y x
       have i₂ := eq2018833
       grind)
    | exact superpose eq2018833 eq23
    | exact resolve eq23 eq2018833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2018833
  have eq2023292 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq25 (σ y) (σ x) X0
       have i₂ := eq2018847
       grind)
    | exact superpose eq2018847 eq25
    | exact resolve eq25 eq2018847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2018847
  have eq2024271 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2023292 X0
       have i₂ := eq21 (σ y) X0
       grind)
    | exact superpose eq21 eq2023292
    | exact resolve eq2023292 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023292
  have eq2025157 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 y y
       have i₂ := eq2024271 X0
       grind)
    | exact superpose eq2024271 eq97
    | (have j1 := eq2024271 X1
       grind)
    | exact resolve eq97 eq2024271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2024271
  have eq2025774 : ∀ X0 X1 : G, (M.op (σ y) X1) = X1 ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq2025157 X1 X1
       have i₂ := eq21 y X1
       grind)
    | exact superpose eq21 eq2025157
    | (have j0 := eq2025157 X0 X1
       grind)
    | exact resolve eq2025157 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025157
  have eq2029421 : ∀ X0 X1 : G, (M.op (M.op (τ (σ y)) X0) (τ (σ y))) = (M.op X0 (M.op (M.op (τ (σ y)) X0) (τ (σ y)))) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq145294 (σ y) X1
       have i₂ := eq2025774 X0 (σ y)
       grind)
    | exact superpose eq2025774 eq145294
    | (have j1 := eq2025774 X1 X1
       grind)
    | exact resolve eq145294 eq2025774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145294 eq2025774
  have eq2030461 : ∀ X0 X1 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq2029421 X1 X1
       have i₂ := eq21 (τ (σ y)) X1
       grind)
    | exact superpose eq21 eq2029421
    | (have j0 := eq2029421 X0 X1
       grind)
    | exact resolve eq2029421 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029421
  have eq2030665 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq2030461 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2030461
    | (have j0 := eq2030461 X0 X0
       grind)
    | exact resolve eq2030461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030461
  have eq2038230 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq2030665 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030665
  have eq2038231 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq2038230 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038230
  have eq2042852 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq144749 y x
       have i₂ := eq2038231 y
       grind)
    | exact superpose eq2038231 eq144749
    | exact resolve eq144749 eq2038231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144749
  have eq2045183 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2042852 x
       have i₂ := eq21 (σ y) x
       grind)
    | exact superpose eq21 eq2042852
    | exact resolve eq2042852 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2042852
  have eq2080700 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2045183 (σ x)
       grind)
    | exact superpose eq2045183 eq16
    | exact resolve eq16 eq2045183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045183
  have eq2081141 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2080700
       have i₂ := eq2038231 x
       grind)
    | exact superpose eq2038231 eq2080700
    | exact resolve eq2080700 eq2038231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038231 eq2080700
  have eq2081142 : False := by grind
  exact eq2081142

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_x_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : x = (τ (σ x)) := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq44
    | (have j0 := eq44 (M.op x y)
       grind)
    | exact resolve eq44 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq16 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq178 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 x y
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq178
    | (have j0 := eq178 (σ x) (σ y)
       grind)
    | exact resolve eq178 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X0 X1) X0
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq179 eq178
    | exact resolve eq178 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq184 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq184
    | (have j0 := eq184 x X0 y
       grind)
    | exact resolve eq184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq185 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq185
       grind)
    | exact resolve eq12 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq676 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq187 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq187
       grind)
    | exact resolve eq12 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq681 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq676
  have eq684 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq672
  have eq697 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq698 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq705 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq758 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq752 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq752 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq752 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq776 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq681 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (σ x) (σ y))
       have r₂ := eq681
       grind)
    | exact resolve eq13 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq777 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq776 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq790 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq684 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq684
       grind)
    | exact resolve eq13 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq791 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq790 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq963 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq777 eq180
    | exact resolve eq180 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq777
  have eq981 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq963
  have eq1010 : x = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq791 eq179
    | exact resolve eq179 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq791
  have eq1028 : x = (k x (M.op x y)) := by grind
  clear eq1010
  have eq1038 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1028 eq41
    | exact resolve eq41 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1039 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1038
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1038
    | exact resolve eq1038 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq697
       grind)
    | exact superpose eq697 eq40
    | exact resolve eq40 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq697
  have eq1104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1103
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1103
    | exact resolve eq1103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1103
  have eq1106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1104
    | exact resolve eq1104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1106 eq698
    | exact resolve eq698 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1349 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1342
       have r₂ := eq27
       grind)
    | exact resolve eq1342 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1358 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1349 eq184
    | exact resolve eq184 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1365 : ∀ X0 : G, y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1358 x
       have i₂ := eq178 sF3 x
       grind)
    | exact superpose eq178 eq1358
    | exact resolve eq1358 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1372 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq184 y y X0
       have i₂ := eq1365 X1
       grind)
    | exact superpose eq1365 eq184
    | (have j1 := eq1365 X1
       grind)
    | exact resolve eq184 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1379 : ∀ X0 X1 : G, (M.op (σ y) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1372 X0 X1
       have i₂ := eq178 y X0
       grind)
    | exact superpose eq178 eq1372
    | (have j0 := eq1372 X0 X1
       grind)
    | exact resolve eq1372 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq1385 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq1379 (M.op X0 X1) X1
       grind)
    | exact superpose eq1379 eq178
    | (have j1 := eq1379 X1 X1
       grind)
    | exact resolve eq178 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq1422 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq1385 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq1385 eq26
    | (have j1 := eq1385 (σ x) X0
       grind)
    | exact resolve eq26 eq1385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1432 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1454 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq178 y X0
       have i₂ := eq1432 X0
       grind)
    | exact superpose eq1432 eq178
    | exact resolve eq178 eq1432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1495 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1454 x
       grind)
    | exact superpose eq1454 eq18
    | (have j1 := eq1454 x
       grind)
    | exact resolve eq18 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1510 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1495
  have eq1541 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1510 eq981
    | exact resolve eq981 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981 eq1510
  have eq1564 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1541 eq1106
    | exact resolve eq1106 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106 eq1541
  have eq1569 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1564
  have eq1811 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq184 y y X0
       have i₂ := eq1569
       grind)
    | exact superpose eq1569 eq184
    | exact resolve eq184 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1817 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1811 X0
       have i₂ := eq178 y X0
       grind)
    | exact superpose eq178 eq1811
    | exact resolve eq1811 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq1922 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq178 y X0
       have i₂ := eq1817 X0
       grind)
    | exact superpose eq1817 eq178
    | exact resolve eq178 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq1973 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1922 x
       grind)
    | exact superpose eq1922 eq18
    | (have j1 := eq1922 x
       grind)
    | exact resolve eq18 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922
  have eq1988 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1973
  have eq1993 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1988 eq28
    | exact resolve eq28 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1996 : (k x (M.op x y)) = (τ (k (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1988 eq99
    | exact resolve eq99 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1988
  have eq2014 : (k x x) = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq1996
    | exact resolve eq1996 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1996
  have eq2017 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1993
    | exact resolve eq1993 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1993
  have eq2020 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1028 eq2014
    | exact resolve eq2014 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq2022 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2017 eq2020
    | exact resolve eq2020 eq2017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2104 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2022 eq758
    | (have j0 := eq758 (M.op x y) X0
       grind)
    | (have r₁ := eq758 (M.op x y) x
       have r₂ := eq2022
       grind)
    | exact resolve eq758 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq2107 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2022 eq745
    | (have j0 := eq745 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq745 (M.op x y) (M.op x y)
       have r₂ := eq2022
       grind)
    | exact resolve eq745 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq2022
  have eq2108 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2107
  have eq2109 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2108
  have eq2112 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2104 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2104
  have eq2152 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2109 eq184
    | exact resolve eq184 eq2109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq2158 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2152 x
       have i₂ := eq178 sF0 x
       grind)
    | exact superpose eq178 eq2152
    | exact resolve eq2152 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2152
  have eq2241 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2158 eq610
    | exact resolve eq610 eq2158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq2158
  have eq2265 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2017 eq2241
    | exact resolve eq2241 eq2017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017 eq2241
  have eq2267 : ∀ X0 : G, y = (M.op (k X0 (M.op x y)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2112 eq2265
    | exact resolve eq2265 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112 eq2265
  have eq3230 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1028 eq2267
    | exact resolve eq2267 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq2267
  have eq3264 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3230
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3230
    | exact resolve eq3230 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3230
  have eq3265 : y = (M.op x y) := by grind
  clear eq3264
  have eq3271 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3265
       grind)
    | exact superpose eq3265 eq24
    | exact resolve eq24 eq3265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3265
  have eq3288 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3271 eq20
    | exact resolve eq20 eq3271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3271
  have eq3327 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3288 eq1039
    | exact resolve eq1039 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq3357 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3327 eq698
    | exact resolve eq698 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq3327
  have eq4455 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3357 eq184
    | exact resolve eq184 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq3357
  have eq4468 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4455 x
       have i₂ := eq178 sF3 x
       grind)
    | exact superpose eq178 eq4455
    | exact resolve eq4455 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455
  have eq4478 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4468 eq178
    | exact resolve eq178 eq4468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468
  have eq4536 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4478 eq26
    | (have j1 := eq4478 (σ x)
       grind)
    | exact resolve eq26 eq4478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478
  have eq4545 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4536
  have eq4549 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4545 eq27
    | exact resolve eq27 eq4545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4545
  have eq4586 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4549
       have r₂ := eq3288
       grind)
    | exact resolve eq4549 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4549
  have eq4592 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4586 eq27
    | exact resolve eq27 eq4586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq4596 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq4586 eq188
    | exact resolve eq188 eq4586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq4634 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4596 x
       have i₂ := eq178 sF2 x
       grind)
    | exact superpose eq178 eq4596
    | exact resolve eq4596 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq4596
  have eq4636 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq3288 eq4592
    | exact resolve eq4592 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288 eq4592
  have eq4775 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4634 eq26
    | (have j1 := eq4634 (σ y)
       grind)
    | exact resolve eq26 eq4634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4634
  have eq4799 : (σ x) = (σ y) := by
    first
    | exact superpose eq4586 eq4775
    | exact resolve eq4775 eq4586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4586 eq4775
  have eq4802 : False := by grind
  exact eq4802

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq73 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq113 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq114 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq123 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq16
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq135 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq114
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq16
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq135
  have eq203 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  clear eq40
  have eq669 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (k X0 X1)) X2) (σ X0)) X2) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq14
    | (have j1 := eq93 X0 X1
       grind)
    | exact resolve eq14 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq863 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X0) ≠ (M.op (M.op (M.op X0 X1) X2) X0) ∨ (M.op (M.op (M.op (M.op X0 X1) X2) X0) X3) = (k X3 (M.op (M.op (M.op X0 X1) X2) X0)) ∨ (k X2 (M.op (M.op (M.op X0 X1) X2) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op (M.op (M.op X0 X1) X2) X0)
       have i₂ := eq86 X2 X0 X1
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 X3 (M.op (M.op (M.op X0 X1) X2) X0)
       have j1 := eq86 X2 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have r₂ := eq86 X0 X1 X2
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq864 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X3) = (k X3 (M.op (M.op (M.op X0 X1) X2) X0)) ∨ (k X2 (M.op (M.op (M.op X0 X1) X2) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq863 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq898 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq60
    | (have j0 := eq60 (σ x) X0 (σ y)
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq60 X1 X2 X0
       grind)
    | exact superpose eq60 eq54
    | exact resolve eq54 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5664 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq203 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq203
    | (have j0 := eq203 y
       grind)
    | exact resolve eq203 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq5692 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5664
  have eq5696 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5692
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq5692
    | exact resolve eq5692 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq5692
  have eq5719 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5696
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq5696 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5696
  have eq5737 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5719 eq141
    | exact resolve eq141 eq5719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq10910 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq864 X1 X2 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq10911 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq10910 X0 X1 X2
       grind)
    | (have r₁ := eq10910 X0 X1 X2
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq10910 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10910
  have eq10935 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10911 X1 (M.op X0 X2) X0
       have i₂ := eq54 X0 X2
       grind)
    | exact superpose eq54 eq10911
    | exact resolve eq10911 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11045 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq64 eq10911
    | exact resolve eq10911 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq11056 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10911 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq10911
    | exact resolve eq10911 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10911
  have eq23362 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5719 eq142
    | exact resolve eq142 eq5719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq5719
  have eq30650 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq23362
       grind)
    | exact superpose eq23362 eq16
    | exact resolve eq16 eq23362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23362
  have eq30711 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5737 eq30650
    | exact resolve eq30650 eq5737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30650
  have eq30716 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq30711
       have r₂ := eq13 x y
       grind)
    | exact resolve eq30711 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30711
  have eq43091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq43098 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq43091
    | exact resolve eq43091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43091
  have eq43109 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq43098
       have r₂ := eq27
       grind)
    | exact resolve eq43098 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43098
  have eq43116 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq43109 eq5737
    | exact resolve eq5737 eq43109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5737 eq43109
  have eq43230 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq43116
       have i₂ := eq30716
       grind)
    | exact superpose eq30716 eq43116
    | exact resolve eq43116 eq30716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43116
  have eq43243 : y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq43230
    | exact resolve eq43230 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43230
  have eq43244 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq43243
  have eq43256 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq43244 eq54
    | exact resolve eq54 eq43244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43244
  have eq43318 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq43256
    | exact resolve eq43256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43256
  have eq43338 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq60 y y X0
       have i₂ := eq43318
       grind)
    | exact superpose eq43318 eq60
    | exact resolve eq60 eq43318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq43385 : ∀ X0 : G, (k X0 (M.op (M.op y X0) y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq10935 y X0 y
       have i₂ := eq43318
       grind)
    | exact superpose eq43318 eq10935
    | exact resolve eq10935 eq43318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43318
  have eq43403 : ∀ X0 : G, x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq43385 X0
       have i₂ := eq54 y X0
       grind)
    | exact superpose eq54 eq43385
    | exact resolve eq43385 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43385
  have eq43424 : ∀ X0 : G, x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43338 X0
       have i₂ := eq54 y X0
       grind)
    | exact superpose eq54 eq43338
    | exact resolve eq43338 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43338
  have eq43952 : ∀ X0 : G, y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 y x
       have i₂ := eq43403 X0
       grind)
    | exact superpose eq43403 eq54
    | (have j1 := eq43403 X0
       grind)
    | exact resolve eq54 eq43403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43403
  have eq44014 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq43952 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43952
    | (have j0 := eq43952 X0
       grind)
    | exact resolve eq43952 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43952
  have eq44016 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44014 y
       have i₂ := eq30716
       grind)
    | exact superpose eq30716 eq44014
    | exact resolve eq44014 eq30716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44014
  have eq44228 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq57 X0 y y
       have i₂ := eq44016
       grind)
    | exact superpose eq44016 eq57
    | exact resolve eq57 eq44016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq44016
  have eq44314 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq44228 x
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq44228
    | exact resolve eq44228 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44228
  have eq46053 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq44314 x
       grind)
    | exact superpose eq44314 eq18
    | (have j1 := eq44314 x
       grind)
    | exact resolve eq18 eq44314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44314
  have eq46121 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq46053
  have eq46808 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq46121 eq11045
    | exact resolve eq11045 eq46121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11045 eq46121
  have eq46941 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq46808 eq123
    | exact resolve eq123 eq46808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq46808
  have eq46966 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq46941
    | exact resolve eq46941 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq46941
  have eq47428 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq46966
       grind)
    | exact superpose eq46966 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq46966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46966
  have eq47441 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47428
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47428
    | exact resolve eq47428 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47428
  have eq47442 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq47441
  have eq50577 : x ≠ x ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have j0 := eq43424 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43424
  have eq50578 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq50577
  have eq50653 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11056 y x
       have i₂ := eq50578
       grind)
    | exact superpose eq50578 eq11056
    | exact resolve eq11056 eq50578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11056 eq50578
  have eq50748 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq669 y x X0
       have i₂ := eq50653
       grind)
    | exact superpose eq50653 eq669
    | (have j0 := eq669 y x x
       grind)
    | exact resolve eq669 eq50653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq50653
  have eq50753 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq50748 X0
       have i₂ := eq54 (σ y) X0
       grind)
    | exact superpose eq54 eq50748
    | exact resolve eq50748 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50748
  have eq50770 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq50753 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50753
    | (have j0 := eq50753 X0
       grind)
    | exact resolve eq50753 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50753
  have eq50778 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq50770 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50770
    | (have j0 := eq50770 X0
       grind)
    | exact resolve eq50770 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50770
  have eq50784 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq50778 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50778
    | (have j0 := eq50778 X0
       grind)
    | exact resolve eq50778 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50778
  have eq50791 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq50784
    | (have j0 := eq50784 X0
       grind)
    | exact resolve eq50784 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50784
  have eq50792 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq50791 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50791
  have eq50799 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50792 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50792
    | (have j0 := eq50792 X0
       grind)
    | exact resolve eq50792 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq50792
  have eq58853 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq903 X0
       have i₂ := eq50799 (M.op sF2 X0)
       grind)
    | exact superpose eq50799 eq903
    | (have j1 := eq50799 X0
       grind)
    | exact resolve eq903 eq50799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq50799
  have eq59008 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq56 eq58853
    | (have j0 := eq58853 X0
       grind)
    | exact resolve eq58853 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq58853
  have eq59026 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq59008
    | (have j0 := eq59008 X0
       grind)
    | exact resolve eq59008 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59008
  have eq59027 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq59026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59026
  have eq59065 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq59027 eq54
    | exact resolve eq54 eq59027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59027
  have eq59438 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59065 eq26
    | (have j1 := eq59065 (σ x)
       grind)
    | exact resolve eq26 eq59065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq59065
  have eq59493 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq59438
  have eq59520 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq59493 eq27
    | exact resolve eq27 eq59493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq59493
  have eq98992 : ∀ X0 : G, (k X0 (M.op (M.op y X0) y)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10935 y X0 x
       have i₂ := eq47442
       grind)
    | exact superpose eq47442 eq10935
    | exact resolve eq10935 eq47442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10935 eq47442
  have eq99023 : ∀ X0 : G, x = (M.op x x) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq98992 X0
       have i₂ := eq54 y X0
       grind)
    | exact superpose eq54 eq98992
    | exact resolve eq98992 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98992
  have eq111649 : ∀ X0 : G, y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq898 x
       have i₂ := eq99023 X0
       grind)
    | exact superpose eq99023 eq898
    | (have j1 := eq99023 X0
       grind)
    | exact resolve eq898 eq99023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq99023
  have eq111815 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq55 eq111649
    | (have j0 := eq111649 X0
       grind)
    | exact resolve eq111649 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq111649
  have eq111841 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq111815 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111815
    | (have j0 := eq111815 X0
       grind)
    | exact resolve eq111815 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111815
  have eq111842 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq111841 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111841
  have eq111852 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq111842 y
       have i₂ := eq30716
       grind)
    | exact superpose eq30716 eq111842
    | exact resolve eq111842 eq30716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30716 eq111842
  have eq112886 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq942 X0 y y
       have i₂ := eq111852
       grind)
    | exact superpose eq111852 eq942
    | exact resolve eq942 eq111852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq111852
  have eq112946 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq112886 x
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq112886
    | exact resolve eq112886 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq112886
  have eq116005 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq112946 x
       grind)
    | exact superpose eq112946 eq18
    | (have j1 := eq112946 x
       grind)
    | exact resolve eq18 eq112946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq112946
  have eq116132 : y = (M.op x y) := by grind
  clear eq116005
  have eq116172 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq116132 eq20
    | exact resolve eq20 eq116132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq116132
  have eq116481 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq116172
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq116172
    | exact resolve eq116172 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq116172
  have eq116531 : False := by grind
  exact eq116531

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq41
    | exact resolve eq41 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1) (σ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq21
    | (have j1 := eq68 X1 X1
       grind)
    | exact resolve eq21 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq178 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq254 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq178 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 (τ X0)
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq256 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq254 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq254
    | (have j0 := eq254 X0
       grind)
    | exact resolve eq254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq259 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq256 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq256
    | (have j0 := eq256 X0
       grind)
    | exact resolve eq256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq584 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 (M.op X1 (τ X0)) X2
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq41
    | (have j1 := eq70 X1 X0
       grind)
    | exact resolve eq41 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq70
  have eq591 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq584 X0 X1 X2
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq584
    | (have j0 := eq584 X0 X1 X2
       grind)
    | exact resolve eq584 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq584
  have eq980 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (τ X0) X1)) X0) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (M.op (τ X0) X1)
       have i₂ := eq23 (τ X0) X1
       grind)
    | exact superpose eq23 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1366 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq166
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq166
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq166 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq1367 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1366
  have eq1645 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq171 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq1646 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1645 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1667 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ (k (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1646 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1646
    | exact resolve eq1646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1681 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) (σ X0) X1
       have i₂ := eq1646 X0
       grind)
    | exact superpose eq1646 eq25
    | (have j1 := eq1646 X0
       grind)
    | exact resolve eq25 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1722 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1681 X0 X1
       have i₂ := eq21 (σ X0) X1
       grind)
    | exact superpose eq21 eq1681
    | (have j0 := eq1681 X0 X1
       grind)
    | exact resolve eq1681 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681
  have eq1728 : ∀ X0 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1667 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1667
    | (have j0 := eq1667 X0
       grind)
    | exact resolve eq1667 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq1730 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1728 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1728
    | (have j0 := eq1728 X0
       grind)
    | exact resolve eq1728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq1739 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 (k X0 X0) X0
       have i₂ := eq1730 X0
       grind)
    | exact superpose eq1730 eq21
    | (have j1 := eq1730 X0
       grind)
    | exact resolve eq21 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1883 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (k (τ X0) (τ X0))
       have i₂ := eq1739 (τ X0)
       grind)
    | exact superpose eq1739 eq71
    | (have j0 := eq71 X0 (τ X0)
       have j1 := eq1739 (τ X0)
       grind)
    | exact resolve eq71 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1739
  have eq1884 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1883 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq1888 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1884 X0
       have j1 := eq259 (τ X0)
       grind)
    | (have r₁ := eq1884 X0
       have r₂ := eq259 (τ X0)
       grind)
    | exact resolve eq1884 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq1884
  have eq1889 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1888 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1888
    | (have j0 := eq1888 X0
       grind)
    | exact resolve eq1888 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1890 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1889 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1889
    | (have j0 := eq1889 X0
       grind)
    | exact resolve eq1889 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889
  have eq1897 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1722 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1722
    | (have j0 := eq1722 (k (τ X0) (τ X0)) X0
       grind)
    | exact resolve eq1722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722
  have eq1948 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1897 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1897
    | (have j0 := eq1897 (k (σ (τ X0)) X0) X0
       grind)
    | exact resolve eq1897 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq1952 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1948 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1948
    | (have j0 := eq1948 (k X0 X0) X0
       grind)
    | exact resolve eq1948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq1991 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (k X0 X0) X0
       have i₂ := eq1952 X0 X1
       grind)
    | exact superpose eq1952 eq21
    | (have j1 := eq1952 X0 (k X0 X0)
       grind)
    | exact resolve eq21 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq2088 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1991 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq2089 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2088 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq2171 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0 (k X0 X0)
       have i₂ := eq2089 X0
       grind)
    | exact superpose eq2089 eq21
    | exact resolve eq21 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq2226 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2171 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2171
    | exact resolve eq2171 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq2361 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ (k X0 X0)) (σ X0) X1
       have i₂ := eq2226 X0
       grind)
    | exact superpose eq2226 eq25
    | exact resolve eq25 eq2226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226
  have eq7757 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1890 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1890
    | (have j0 := eq1890 (σ X0)
       grind)
    | exact resolve eq1890 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890
  have eq7822 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7757 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq7757
    | (have j0 := eq7757 X0
       grind)
    | exact resolve eq7757 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7757
  have eq7849 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7822 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7822
    | (have j0 := eq7822 X0
       grind)
    | exact resolve eq7822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7822
  have eq19081 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7849 (τ X0)
       have i₂ := eq591 X0 (τ X0) X0
       grind)
    | exact superpose eq591 eq7849
    | (have j0 := eq7849 (τ X0)
       have j1 := eq591 X0 (τ X0) x
       grind)
    | exact resolve eq7849 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq7849
  have eq19110 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq19081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19081
  have eq19132 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19110 X0
       have i₂ := eq18 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq19110
    | (have j0 := eq19110 X0
       grind)
    | exact resolve eq19110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19110
  have eq19152 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19132 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq19132
    | (have j0 := eq19132 X0
       grind)
    | exact resolve eq19132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19132
  have eq19156 : ∀ X0 : G, (k X0 X0) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19152 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19152
    | (have j0 := eq19152 X0
       grind)
    | exact resolve eq19152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19152
  have eq21112 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23 x y
       have i₂ := eq1367
       grind)
    | exact superpose eq1367 eq23
    | exact resolve eq23 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq21183 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq21112
  have eq30209 : ∀ X0 X1 : G, (τ (σ (M.op (τ (σ X0)) X1))) = (k (τ (σ (M.op (τ (σ X0)) X1))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (σ (M.op (τ (σ X0)) X1)) X0
       have i₂ := eq980 (σ X0) X1
       grind)
    | exact superpose eq980 eq35
    | (have j1 := eq980 (σ X0) X1
       grind)
    | exact resolve eq35 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq30243 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (k (M.op (τ (σ X0)) X1) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30209 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq30209
    | (have j0 := eq30209 X0 X1
       grind)
    | exact resolve eq30209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30209
  have eq30286 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30243 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30243
    | (have j0 := eq30243 X0 X1
       grind)
    | exact resolve eq30243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30243
  have eq30316 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30286 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30286
    | (have j0 := eq30286 X0 X1
       grind)
    | exact resolve eq30286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30286
  have eq30337 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30316 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30316
    | (have j0 := eq30316 X0 X1
       grind)
    | exact resolve eq30316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30316
  have eq146910 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq19156 (σ X0)
       grind)
    | exact superpose eq19156 eq35
    | (have j1 := eq19156 (σ X0)
       grind)
    | exact resolve eq35 eq19156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19156
  have eq146997 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq146910 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq146910
    | (have j0 := eq146910 X0
       grind)
    | exact resolve eq146910 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146910
  have eq147045 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (M.op X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq146997 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq146997
    | (have j0 := eq146997 X0
       grind)
    | exact resolve eq146997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146997
  have eq147065 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (M.op X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq147045 X0
       have i₂ := eq35 (σ X0) X0
       grind)
    | exact superpose eq35 eq147045
    | (have j0 := eq147045 X0
       grind)
    | exact resolve eq147045 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq147045
  have eq147075 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq147065 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq147065
    | (have j0 := eq147065 X0
       grind)
    | exact resolve eq147065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147065
  have eq147082 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq147075 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq147075
    | (have j0 := eq147075 X0
       grind)
    | exact resolve eq147075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147075
  have eq147103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30337 X0 X0
       have i₂ := eq147082 X0
       grind)
    | exact superpose eq147082 eq30337
    | (have j0 := eq30337 X0 X0
       have j1 := eq147082 X0
       grind)
    | exact resolve eq30337 eq147082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30337 eq147082
  have eq147208 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq147103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147103
  have eq147264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq147208 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq147208 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq147208 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147208
  have eq148100 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2361 X0 X1
       have i₂ := eq147264 X0
       grind)
    | exact superpose eq147264 eq2361
    | exact resolve eq2361 eq147264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361
  have eq148348 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq147264 (σ X0)
       grind)
    | exact superpose eq147264 eq15
    | exact resolve eq15 eq147264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148472 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq148348 X0
       have i₂ := eq147264 X0
       grind)
    | exact superpose eq147264 eq148348
    | exact resolve eq148348 eq147264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147264 eq148348
  have eq452720 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23 (σ x) (σ y)
       have i₂ := eq21183
       grind)
    | exact superpose eq21183 eq23
    | exact resolve eq23 eq21183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21183
  have eq453011 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq452720
  have eq453304 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq453011
       have i₂ := eq148472 x
       grind)
    | exact superpose eq148472 eq453011
    | exact resolve eq453011 eq148472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148472 eq453011
  have eq453996 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq453304
       grind)
    | exact superpose eq453304 eq10
    | exact resolve eq10 eq453304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453304
  have eq454537 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq453996
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq453996
    | exact resolve eq453996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453996
  have eq454538 : x = (M.op x x) := by grind
  clear eq454537
  have eq454639 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq148100 x X0
       have i₂ := eq454538
       grind)
    | exact superpose eq454538 eq148100
    | exact resolve eq148100 eq454538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148100
  have eq454761 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 x x X0
       have i₂ := eq454538
       grind)
    | exact superpose eq454538 eq25
    | exact resolve eq25 eq454538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq454538
  have eq455146 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq454761 X0
       have i₂ := eq21 x X0
       grind)
    | exact superpose eq21 eq454761
    | exact resolve eq454761 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454761
  have eq455233 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq454639 X0
       have i₂ := eq21 (σ x) X0
       grind)
    | exact superpose eq21 eq454639
    | exact resolve eq454639 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq454639
  have eq460935 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq455233 (σ y)
       grind)
    | exact superpose eq455233 eq16
    | exact resolve eq16 eq455233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455233
  have eq461558 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq460935
       have i₂ := eq455146 y
       grind)
    | exact superpose eq455146 eq460935
    | exact resolve eq460935 eq455146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455146 eq460935
  have eq461559 : False := by grind
  exact eq461559

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq33
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq28
    | exact resolve eq28 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq37 X1 X2 X0
       grind)
    | exact superpose eq37 eq33
    | exact resolve eq33 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq68 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq33
    | (have j1 := eq68 X1 X1
       grind)
    | exact resolve eq33 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq182 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq180 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq190 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 (τ X0) X1
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq192 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq190
    | (have j0 := eq190 X0 X1
       grind)
    | exact resolve eq190 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq195 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq192
    | (have j0 := eq192 X0 X1
       grind)
    | exact resolve eq192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq552 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (M.op X1 (τ X0)) X2
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq28
    | (have j1 := eq70 X1 X0
       grind)
    | exact resolve eq28 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq70
  have eq559 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq552 X0 X1 X2
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq552
    | (have j0 := eq552 X0 X1 X2
       grind)
    | exact resolve eq552 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq552
  have eq1194 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq166
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq166
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq166 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq1195 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1194
  have eq1727 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq172 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq1728 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1727 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1753 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ (k (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1728 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1728
    | exact resolve eq1728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1767 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) (σ X0) X1
       have i₂ := eq1728 X0
       grind)
    | exact superpose eq1728 eq37
    | (have j1 := eq1728 X0
       grind)
    | exact resolve eq37 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq1813 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1767 X0 X1
       have i₂ := eq33 (σ X0) X1
       grind)
    | exact superpose eq33 eq1767
    | (have j0 := eq1767 X0 X1
       grind)
    | exact resolve eq1767 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq1819 : ∀ X0 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1753 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1753
    | (have j0 := eq1753 X0
       grind)
    | exact resolve eq1753 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1822 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1819 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1819
    | (have j0 := eq1819 X0
       grind)
    | exact resolve eq1819 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq1831 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 (k X0 X0) X0
       have i₂ := eq1822 X0
       grind)
    | exact superpose eq1822 eq33
    | (have j1 := eq1822 X0
       grind)
    | exact resolve eq33 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822
  have eq1999 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0 (k (τ X0) (τ X0))
       have i₂ := eq1831 (τ X0)
       grind)
    | exact superpose eq1831 eq71
    | (have j0 := eq71 X0 (τ X0)
       have j1 := eq1831 (τ X0)
       grind)
    | exact resolve eq71 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1831
  have eq2000 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1999 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2004 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq2000 X0
       have j1 := eq12 (σ (k (τ X0) (τ X0))) X0
       grind)
    | (have r₁ := eq2000 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq2000 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq2005 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2004 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2004
    | (have j0 := eq2004 X0
       grind)
    | exact resolve eq2004 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq2006 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2005 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2005
    | (have j0 := eq2005 X0
       grind)
    | exact resolve eq2005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2007 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2006 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq2006
    | (have j0 := eq2006 X0
       grind)
    | exact resolve eq2006 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq4806 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1813 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1813
    | (have j0 := eq1813 (k (τ X0) (τ X0)) X0
       grind)
    | exact resolve eq1813 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq4870 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4806 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4806
    | (have j0 := eq4806 (k (σ (τ X0)) X0) X0
       grind)
    | exact resolve eq4806 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4806
  have eq4882 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4870 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4870
    | (have j0 := eq4870 (k X0 X0) X0
       grind)
    | exact resolve eq4870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4870
  have eq5087 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 (k X0 X0) X0
       have i₂ := eq4882 X0 X1
       grind)
    | exact superpose eq4882 eq33
    | (have j1 := eq4882 X0 (k X0 X0)
       grind)
    | exact resolve eq33 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4882
  have eq5205 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5087 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5087
  have eq5206 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5205
  have eq5420 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 X0 (k X0 X0)
       have i₂ := eq5206 X0
       grind)
    | exact superpose eq5206 eq33
    | exact resolve eq33 eq5206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5206
  have eq5492 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5420 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq5420
    | exact resolve eq5420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5420
  have eq10915 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2007 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2007
    | exact resolve eq2007 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10936 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (k (σ X0) (σ X0)) X0
       have i₂ := eq2007 (σ X0)
       grind)
    | exact superpose eq2007 eq22
    | (have j1 := eq2007 (σ X0)
       grind)
    | exact resolve eq22 eq2007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq10979 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10936 x
       have i₂ := eq22 (σ x) x
       grind)
    | exact superpose eq22 eq10936
    | (have j0 := eq10936 X0
       grind)
    | exact resolve eq10936 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10936
  have eq10994 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10915 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq10915
    | (have j0 := eq10915 X0
       grind)
    | exact resolve eq10915 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10915
  have eq11015 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10979 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10979
    | (have j0 := eq10979 X0
       grind)
    | exact resolve eq10979 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10979
  have eq11029 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10994 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq10994
    | (have j0 := eq10994 X0
       grind)
    | exact resolve eq10994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10994
  have eq11049 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11015 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq11015
    | (have j0 := eq11015 X0
       grind)
    | exact resolve eq11015 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11015
  have eq11063 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11029 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11029
    | (have j0 := eq11029 X0
       grind)
    | exact resolve eq11029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11029
  have eq11078 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11049 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11049
    | (have j0 := eq11049 X0
       grind)
    | exact resolve eq11049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11049
  have eq11105 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq11078 X0
       have j1 := eq195 X0 (k X0 X0)
       grind)
    | (have r₁ := eq11078 X0
       have r₂ := eq195 X0 x
       grind)
    | exact resolve eq11078 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq11078
  have eq11542 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11105 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq11105
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq11105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11592 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11542 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11542
  have eq11629 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq11592 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq11592 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq11592 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11592
  have eq11736 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq11629 (τ X0)
       grind)
    | exact superpose eq11629 eq18
    | exact resolve eq18 eq11629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17483 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq11063 (τ X0)
       have i₂ := eq559 X0 (τ X0) X0
       grind)
    | exact superpose eq559 eq11063
    | (have j0 := eq11063 (τ X0)
       have j1 := eq559 X0 (τ X0) x
       grind)
    | exact resolve eq11063 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11063
  have eq17484 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq11105 (τ X0)
       have i₂ := eq559 X0 (τ X0) X0
       grind)
    | exact superpose eq559 eq11105
    | (have j1 := eq559 X0 (τ X0) x
       grind)
    | exact resolve eq11105 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq11105
  have eq17520 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq17484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17484
  have eq17521 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq17483 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17483
  have eq17540 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17520 X0
       have i₂ := eq11629 (τ X0)
       grind)
    | exact superpose eq11629 eq17520
    | (have j0 := eq17520 X0
       grind)
    | exact resolve eq17520 eq11629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11629 eq17520
  have eq17541 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq17521 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq17521 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq17521 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17521
  have eq17561 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17540 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq17540
    | (have j0 := eq17540 X0
       grind)
    | exact resolve eq17540 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17540
  have eq17562 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17541 X0
       have i₂ := eq18 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq17541
    | (have j0 := eq17541 X0
       grind)
    | exact resolve eq17541 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17541
  have eq17570 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17562 X0
       have i₂ := eq11736 X0
       grind)
    | exact superpose eq11736 eq17562
    | (have j0 := eq17562 X0
       grind)
    | exact resolve eq17562 eq11736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11736 eq17562
  have eq17574 : ∀ X0 : G, (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17570 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq17570
    | (have j0 := eq17570 X0
       grind)
    | exact resolve eq17570 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17570
  have eq17578 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17574 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17574
    | (have j0 := eq17574 X0
       grind)
    | exact resolve eq17574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17574
  have eq17580 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17578 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq17578
    | (have j0 := eq17578 X0
       grind)
    | exact resolve eq17578 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq17578
  have eq19397 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35 x y
       have i₂ := eq1195
       grind)
    | exact superpose eq1195 eq35
    | exact resolve eq35 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq19462 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq19397
  have eq25899 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq17580 X0
       grind)
    | exact superpose eq17580 eq10
    | (have j1 := eq17580 X0
       grind)
    | exact resolve eq10 eq17580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17580
  have eq57935 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq25899 X0
       grind)
    | exact superpose eq25899 eq11
    | (have j1 := eq25899 X0
       grind)
    | exact resolve eq11 eq25899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58055 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57935 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57935
    | (have j0 := eq57935 X0
       grind)
    | exact resolve eq57935 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57935
  have eq58339 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58055 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58055
    | (have j0 := eq58055 (σ X0)
       grind)
    | exact resolve eq58055 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58055
  have eq58650 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58339 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq58339
    | (have j0 := eq58339 X0
       grind)
    | exact resolve eq58339 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58339
  have eq58676 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58650 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58650
    | (have j0 := eq58650 X0
       grind)
    | exact resolve eq58650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58650
  have eq58678 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq58676 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq58676
    | (have j0 := eq58676 X0
       grind)
    | exact resolve eq58676 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58676
  have eq58730 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0
       have i₂ := eq58678 X0
       grind)
    | exact superpose eq58678 eq176
    | (have j0 := eq176 X0 X0
       have j1 := eq58678 X0
       grind)
    | (have r₁ := eq176 X0 X0
       have r₂ := eq58678 X0
       grind)
    | exact resolve eq176 eq58678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq58678
  have eq58862 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq58730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58730
  have eq58863 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq58862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58862
  have eq62349 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ X0) X1) (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0) (σ X0)
       have i₂ := eq58863 X0
       grind)
    | exact superpose eq58863 eq97
    | (have j1 := eq58863 X0
       grind)
    | exact resolve eq97 eq58863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq58863
  have eq62476 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62349 X0 X1
       have i₂ := eq33 (σ X0) X1
       grind)
    | exact superpose eq33 eq62349
    | (have j0 := eq62349 X0 X1
       grind)
    | exact resolve eq62349 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62349
  have eq62582 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5492 X0
       have i₂ := eq62476 X0 X1
       grind)
    | exact superpose eq62476 eq5492
    | (have j1 := eq62476 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq5492 eq62476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5492 eq62476
  have eq139853 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62582 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62582
  have eq139854 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq139853 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139853
  have eq140166 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ (M.op X0 X0)) (σ X0) X1
       have i₂ := eq139854 X0
       grind)
    | exact superpose eq139854 eq37
    | exact resolve eq37 eq139854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139854
  have eq213359 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq17561 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17561
  have eq213366 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq213359 X0
       have j1 := eq25899 X0
       grind)
    | (have r₁ := eq213359 X0
       have r₂ := eq25899 X0
       grind)
    | exact resolve eq213359 eq25899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25899 eq213359
  have eq213460 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq213366 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq213366
    | exact resolve eq213366 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213366
  have eq214060 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq213460 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq213460
    | exact resolve eq213460 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq213460
  have eq214128 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq214060 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq214060
    | exact resolve eq214060 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214060
  have eq215417 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq214128 (σ X0)
       grind)
    | exact superpose eq214128 eq15
    | exact resolve eq15 eq214128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215562 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq215417 X0
       have i₂ := eq214128 X0
       grind)
    | exact superpose eq214128 eq215417
    | exact resolve eq215417 eq214128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214128 eq215417
  have eq404338 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35 (σ x) (σ y)
       have i₂ := eq19462
       grind)
    | exact superpose eq19462 eq35
    | exact resolve eq35 eq19462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq19462
  have eq404543 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq404338
  have eq404750 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq404543
       have i₂ := eq215562 x
       grind)
    | exact superpose eq215562 eq404543
    | exact resolve eq404543 eq215562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215562 eq404543
  have eq405155 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq404750
       grind)
    | exact superpose eq404750 eq10
    | exact resolve eq10 eq404750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404750
  have eq405653 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq405155
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq405155
    | exact resolve eq405155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405155
  have eq405654 : x = (M.op x x) := by grind
  clear eq405653
  have eq405763 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq140166 x X0
       have i₂ := eq405654
       grind)
    | exact superpose eq405654 eq140166
    | exact resolve eq140166 eq405654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140166
  have eq405865 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 x x X0
       have i₂ := eq405654
       grind)
    | exact superpose eq405654 eq37
    | exact resolve eq37 eq405654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq405654
  have eq406125 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq405865 X0
       have i₂ := eq33 x X0
       grind)
    | exact superpose eq33 eq405865
    | exact resolve eq405865 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405865
  have eq406214 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq405763 X0
       have i₂ := eq33 (σ x) X0
       grind)
    | exact superpose eq33 eq405763
    | exact resolve eq405763 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq405763
  have eq414496 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq406214 (σ y)
       grind)
    | exact superpose eq406214 eq16
    | exact resolve eq16 eq406214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406214
  have eq415049 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq414496
       have i₂ := eq406125 y
       grind)
    | exact superpose eq406125 eq414496
    | exact resolve eq414496 eq406125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406125 eq414496
  have eq415050 : False := by grind
  exact eq415050

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  clear eq18
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X0 X1) X0
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq34
    | exact resolve eq34 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq168 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq70 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq70 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq12 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq181 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq167 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq182 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq180 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq183 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq181 X0
       have j1 := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq181 X0
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq181 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq186 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq183 X0
       have j1 := eq182 X0 (σ (k X0 X0))
       grind)
    | (have r₁ := eq183 X0
       have r₂ := eq182 X0 x
       grind)
    | exact resolve eq183 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq183
  have eq187 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq186
    | exact resolve eq186 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq195 : ∀ X0 : G, (k (k X0 X0) X0) = (τ (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq187 X0
       grind)
    | exact superpose eq187 eq10
    | exact resolve eq10 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq195
    | exact resolve eq195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq319 : ∀ X0 X1 X2 : G, (σ (k (k X1 (τ X0)) X2)) = (k (M.op X0 (σ X1)) (σ X2)) ∨ (σ X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X0 X2
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1461 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq166
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq166
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq166 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1462 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1461
  have eq13180 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq319
  have eq13239 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq13180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13180
  have eq13269 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13239 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13239
    | (have j0 := eq13239 X0
       grind)
    | exact resolve eq13239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13239
  have eq13359 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13269 X0
       have i₂ := eq187 X0
       grind)
    | exact superpose eq187 eq13269
    | (have j0 := eq13269 X0
       grind)
    | exact resolve eq13269 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13269
  have eq13413 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq13359 X0
       grind)
    | exact superpose eq13359 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq13359 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq13359 X0
       grind)
    | exact resolve eq12 eq13359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13483 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13484 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13413
  have eq13913 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13484 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13484
    | exact resolve eq13484 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13484
  have eq14095 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13913 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq13913
    | (have j0 := eq13913 X0 X1
       grind)
    | exact resolve eq13913 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13913
  have eq14122 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14095 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14095
    | (have j0 := eq14095 X0 X1
       grind)
    | exact resolve eq14095 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14095
  have eq14163 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0
       have i₂ := eq14122 X0 X1
       grind)
    | exact superpose eq14122 eq215
    | (have j1 := eq14122 X0 (M.op X0 X0)
       grind)
    | exact resolve eq215 eq14122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq14122
  have eq14548 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq14163 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14163
  have eq14549 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq14548 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14548
  have eq14619 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq14549 (σ X0)
       grind)
    | exact superpose eq14549 eq23
    | exact resolve eq23 eq14549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq14967 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14619 X0
       have i₂ := eq13359 X0
       grind)
    | exact superpose eq13359 eq14619
    | (have j1 := eq13359 X0
       grind)
    | exact resolve eq14619 eq13359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13359 eq14619
  have eq15171 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14967 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14967
    | (have j0 := eq14967 X0
       grind)
    | exact resolve eq14967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14967
  have eq15735 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq15171 X0
       grind)
    | exact superpose eq15171 eq187
    | (have j1 := eq15171 X0
       grind)
    | exact resolve eq187 eq15171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq15171
  have eq15961 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq15735 X0
       have j1 := eq13483 X0
       grind)
    | (have r₁ := eq15735 X0
       have r₂ := eq13483 X0
       grind)
    | exact resolve eq15735 eq13483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13483 eq15735
  have eq16092 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15961 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15961
    | exact resolve eq15961 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16172 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0) (σ X0)
       have i₂ := eq15961 X0
       grind)
    | exact superpose eq15961 eq34
    | exact resolve eq34 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16286 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq16092 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq16092
    | exact resolve eq16092 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16092
  have eq16302 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq16286 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16286
    | exact resolve eq16286 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16286
  have eq16350 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14549 x
       have i₂ := eq1462
       grind)
    | exact superpose eq1462 eq14549
    | exact resolve eq14549 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14549
  have eq16356 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36 x x
       have i₂ := eq1462
       grind)
    | exact superpose eq1462 eq36
    | exact resolve eq36 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq16468 : (σ x) = (σ (k x x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16356
       have i₂ := eq15961 x
       grind)
    | exact superpose eq15961 eq16356
    | exact resolve eq16356 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16356
  have eq16474 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq16350
       have r₂ := eq12 x (σ x)
       grind)
    | (have r₁ := eq16350
       have r₂ := eq12 x x
       grind)
    | exact resolve eq16350 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16350
  have eq16560 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16468
       have i₂ := eq16302 x
       grind)
    | exact superpose eq16302 eq16468
    | exact resolve eq16468 eq16302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16468
  have eq16566 : (σ x) = (σ (k x x)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16474
       have i₂ := eq15961 x
       grind)
    | exact superpose eq15961 eq16474
    | exact resolve eq16474 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16474
  have eq16652 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16560
       have i₂ := eq15961 x
       grind)
    | exact superpose eq15961 eq16560
    | exact resolve eq16560 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16560
  have eq16658 : (σ x) = (σ (M.op x x)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16566
       have i₂ := eq16302 x
       grind)
    | exact superpose eq16302 eq16566
    | exact resolve eq16566 eq16302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16566
  have eq16744 : y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16652
       have i₂ := eq16302 x
       grind)
    | exact superpose eq16302 eq16652
    | exact resolve eq16652 eq16302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16652
  have eq16750 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16658
       have i₂ := eq15961 x
       grind)
    | exact superpose eq15961 eq16658
    | exact resolve eq16658 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16658
  have eq16780 : y = (k y x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16750
       have i₂ := eq16302 x
       grind)
    | exact superpose eq16302 eq16750
    | exact resolve eq16750 eq16302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16750
  have eq17199 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16172 X0
       have i₂ := eq16302 X0
       grind)
    | exact superpose eq16302 eq16172
    | exact resolve eq16172 eq16302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16172
  have eq18247 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq34 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq17199 X0
       grind)
    | exact superpose eq17199 eq34
    | exact resolve eq34 eq17199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18250 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ (M.op X0 X0)) (σ X0) X1
       have i₂ := eq17199 X0
       grind)
    | exact superpose eq17199 eq38
    | exact resolve eq38 eq17199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17199
  have eq75217 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq166
       have i₂ := eq16780
       grind)
    | exact superpose eq16780 eq166
    | exact resolve eq166 eq16780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq16780
  have eq75227 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq75217
       have i₂ := eq15961 x
       grind)
    | exact superpose eq15961 eq75217
    | exact resolve eq75217 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75217
  have eq75232 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq75227
       have i₂ := eq16302 x
       grind)
    | exact superpose eq16302 eq75227
    | exact resolve eq75227 eq16302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75227
  have eq75233 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq75232
  have eq75236 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq75233
       have i₂ := eq15961 x
       grind)
    | exact superpose eq15961 eq75233
    | exact resolve eq75233 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961 eq75233
  have eq75241 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq75236
       have i₂ := eq16302 x
       grind)
    | exact superpose eq16302 eq75236
    | exact resolve eq75236 eq16302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16302 eq75236
  have eq75242 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq75241
  have eq1321902 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75242
       have i₂ := eq16744
       grind)
    | exact superpose eq16744 eq75242
    | exact resolve eq75242 eq16744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16744 eq75242
  have eq1321904 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq1321902
  have eq1321905 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq1321904
  have eq1327095 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1321905
       grind)
    | exact superpose eq1321905 eq10
    | exact resolve eq10 eq1321905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321905
  have eq1327655 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1327095
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1327095
    | exact resolve eq1327095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327095
  have eq1332618 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1327655
       grind)
    | exact superpose eq1327655 eq10
    | exact resolve eq10 eq1327655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327655
  have eq1333190 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1332618
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1332618
    | exact resolve eq1332618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332618
  have eq1333191 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq1333190
  have eq1333421 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18247 x
       have i₂ := eq1333191
       grind)
    | exact superpose eq1333191 eq18247
    | exact resolve eq18247 eq1333191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18247
  have eq1333908 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36 x x
       have i₂ := eq1333191
       grind)
    | exact superpose eq1333191 eq36
    | exact resolve eq36 eq1333191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1333191
  have eq1379053 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1333421
       grind)
    | exact superpose eq1333421 eq16
    | exact resolve eq16 eq1333421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333421
  have eq1383700 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1379053
       have i₂ := eq1333908
       grind)
    | exact superpose eq1333908 eq1379053
    | exact resolve eq1379053 eq1333908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333908 eq1379053
  have eq1383705 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by grind
  clear eq1383700
  have eq1383706 : x = (M.op x x) := by grind
  clear eq1383705
  have eq1383767 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18250 x X0
       have i₂ := eq1383706
       grind)
    | exact superpose eq1383706 eq18250
    | exact resolve eq18250 eq1383706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18250
  have eq1384190 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq38 x x X0
       have i₂ := eq1383706
       grind)
    | exact superpose eq1383706 eq38
    | exact resolve eq38 eq1383706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1383706
  have eq1384562 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1384190 X0
       have i₂ := eq34 x X0
       grind)
    | exact superpose eq34 eq1384190
    | exact resolve eq1384190 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384190
  have eq1384949 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1383767 X0
       have i₂ := eq34 (σ x) X0
       grind)
    | exact superpose eq34 eq1383767
    | exact resolve eq1383767 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1383767
  have eq1403571 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1384949 (σ y)
       grind)
    | exact superpose eq1384949 eq16
    | exact resolve eq16 eq1384949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384949
  have eq1404628 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1403571
       have i₂ := eq1384562 y
       grind)
    | exact superpose eq1384562 eq1403571
    | exact resolve eq1403571 eq1384562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384562 eq1403571
  have eq1404629 : False := by grind
  exact eq1404629
