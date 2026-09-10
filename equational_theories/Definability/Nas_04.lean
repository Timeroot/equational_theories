import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
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
  clear eq24 eq36
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq116 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq116 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq43
    | exact resolve eq43 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq121 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq117 y
       grind)
    | exact superpose eq117 eq74
    | exact resolve eq74 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq122 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq49
    | exact resolve eq49 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq123 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq86
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq86
    | exact resolve eq86 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq124 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq123
       have i₂ := eq117 y
       grind)
    | exact superpose eq117 eq123
    | exact resolve eq123 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq125 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq122
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq122
    | exact resolve eq122 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq121
    | exact resolve eq121 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq127 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq120
    | exact resolve eq120 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq120
  have eq262 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq262
    | exact resolve eq262 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq109 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq922
    | exact resolve eq922 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq926 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq923
       have r₂ := eq27
       grind)
    | exact resolve eq923 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq928 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq926
    | exact resolve eq926 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq931 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq928 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq928
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq928
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq928
       grind)
    | exact resolve eq12 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq933 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq928 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq928 eq14
    | exact resolve eq14 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq51 eq934
    | exact resolve eq934 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq934
  have eq936 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq933
    | exact resolve eq933 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq938 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq931
       have r₂ := eq26
       grind)
    | exact resolve eq931 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq952 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq935 eq124
    | exact resolve eq124 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq935
  have eq1016 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq928 eq952
    | exact resolve eq952 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq952
  have eq1030 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq1016
  have eq1032 : (M.op (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq126
       have i₂ := eq1030
       grind)
    | exact superpose eq1030 eq126
    | exact resolve eq126 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1044 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1032
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1032
    | exact resolve eq1032 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1063 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq938 eq109
    | exact resolve eq109 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq1066 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1063
  have eq1073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1066 eq1044
    | exact resolve eq1044 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq1066
  have eq1085 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1073
  have eq1092 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1085
       have r₂ := eq27
       grind)
    | exact resolve eq1085 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1099 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq1092
       grind)
    | exact superpose eq1092 eq14
    | exact resolve eq14 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1100 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq50 eq1099
    | exact resolve eq1099 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1106 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1100 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1100
    | (have j0 := eq1100 x
       grind)
    | exact resolve eq1100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1119 : (σ (M.op y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq126
       have i₂ := eq1100 y
       grind)
    | exact superpose eq1100 eq126
    | exact resolve eq126 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq1100
  have eq1128 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq1106
       grind)
    | exact superpose eq1106 eq127
    | exact resolve eq127 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq1106
  have eq1142 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1128
    | exact resolve eq1128 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1198 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1142 eq54
    | exact resolve eq54 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1260 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1119
       have i₂ := eq1092
       grind)
    | exact superpose eq1092 eq1119
    | exact resolve eq1119 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq1119
  have eq1275 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1260
  have eq1277 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1275
    | exact resolve eq1275 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1284 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1277 eq54
    | exact resolve eq54 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1277
  have eq1402 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1284 eq1198
    | exact resolve eq1198 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq1284
  have eq1418 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1402 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1478 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1418
    | (have j0 := eq1418 (σ x)
       grind)
    | exact resolve eq1418 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1478 eq1142
    | exact resolve eq1142 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq1478
  have eq1523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1511
  have eq1529 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1523
       have r₂ := eq27
       grind)
    | exact resolve eq1523 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1531 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1529 eq936
    | (have r₁ := eq936
       have r₂ := eq1529
       grind)
    | exact resolve eq936 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq1533 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1529 eq265
    | exact resolve eq265 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq1535 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1529 eq27
    | exact resolve eq27 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1536 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq1531
  have eq1643 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq1533
    | (have j0 := eq1533 X0 (σ y)
       grind)
    | exact resolve eq1533 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1680 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq1529 eq1643
    | exact resolve eq1643 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1753 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1680 eq26
    | (have j1 := eq1680 (σ x)
       grind)
    | exact resolve eq26 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1680
  have eq1761 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1529 eq1753
    | exact resolve eq1753 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529 eq1753
  have eq1774 : (τ (σ x)) = (M.op x x) := by
    first
    | exact superpose eq1761 eq125
    | exact resolve eq125 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq1761
  have eq1786 : x = (M.op x x) := by
    first
    | exact superpose eq28 eq1774
    | exact resolve eq1774 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1774
  have eq2167 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1536 eq109
    | exact resolve eq109 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq1536
  have eq2170 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq2167
  have eq2176 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq2170
       have r₂ := eq1535
       grind)
    | exact resolve eq2170 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170
  have eq2185 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq2176
       grind)
    | exact superpose eq2176 eq14
    | exact resolve eq14 eq2176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2186 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq50 eq2185
    | exact resolve eq2185 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2185
  have eq2274 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2186 x
       grind)
    | exact superpose eq2186 eq18
    | (have j1 := eq2186 x
       grind)
    | exact resolve eq18 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2186
  have eq2287 : x = (M.op x y) := by
    first
    | (have i₁ := eq2274
       have i₂ := eq1786
       grind)
    | exact superpose eq1786 eq2274
    | exact resolve eq2274 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786 eq2274
  have eq2297 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2287 eq20
    | exact resolve eq20 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2287
  have eq2332 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2297
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2297
    | exact resolve eq2297 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2297
  have eq2338 : False := by grind
  exact eq2338

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq82 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq279 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq81 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq280 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq290 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq280 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq280
    | (have j0 := eq280 (τ X0)
       grind)
    | exact resolve eq280 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq290
    | (have j0 := eq290 X0
       grind)
    | exact resolve eq290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq295 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq292 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq292
    | (have j0 := eq292 X0
       grind)
    | exact resolve eq292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq301 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq295 (τ X0)
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq295
    | (have j0 := eq295 (τ X0)
       grind)
    | exact resolve eq295 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq2766 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2786 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq82 X0 (σ X0)
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2808 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2786 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786
  have eq2815 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2766 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq2766
    | (have j0 := eq2766 X0 X1
       grind)
    | exact resolve eq2766 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq2824 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq2815 X0 X1
       grind)
    | exact superpose eq2815 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq2815 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq2815 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq2815 X0 X0
       grind)
    | exact resolve eq13 eq2815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2851 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2815 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815
  have eq2854 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2824 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq2863 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2854 X0 X1
       have j1 := eq2851 X0 X1
       grind)
    | (have r₁ := eq2854 X0 X1
       have r₂ := eq2851 (k X1 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq2854 X0 X1
       have r₂ := eq2851 (M.op X1 X1) (k X1 X0)
       grind)
    | (have r₁ := eq2854 X0 X1
       have r₂ := eq2851 X0 X1
       grind)
    | exact resolve eq2854 eq2851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854
  have eq2870 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2851 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2851
  have eq2929 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq2870 X0
       grind)
    | exact superpose eq2870 eq12
    | (have j1 := eq2870 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2870 X0
       grind)
    | exact resolve eq12 eq2870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2870
  have eq2951 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2929 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq2963 : ∀ X0 : G, (τ (σ (k X0 X0))) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2951 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2951
    | exact resolve eq2951 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2978 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq2951 X0
       grind)
    | exact superpose eq2951 eq11
    | (have j1 := eq2951 X0
       grind)
    | exact resolve eq11 eq2951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951
  have eq3055 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2978 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2978
    | (have j0 := eq2978 X0
       grind)
    | exact resolve eq2978 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978
  have eq3068 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2963 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq2963
    | (have j0 := eq2963 X0
       grind)
    | exact resolve eq2963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963
  have eq3162 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq3055 (τ X0)
       grind)
    | exact superpose eq3055 eq17
    | (have j1 := eq3055 (τ X0)
       grind)
    | exact resolve eq17 eq3055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055
  have eq3207 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3162 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3162
    | (have j0 := eq3162 X0
       grind)
    | exact resolve eq3162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162
  have eq3252 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3207 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq3207
    | (have j0 := eq3207 X0
       grind)
    | exact resolve eq3207 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3207
  have eq3411 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq3068 X0
       grind)
    | exact superpose eq3068 eq10
    | (have j1 := eq3068 X0
       grind)
    | exact resolve eq10 eq3068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068
  have eq3461 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3411 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3411
    | (have j0 := eq3411 X0
       grind)
    | exact resolve eq3411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3411
  have eq3615 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3461 X0
       grind)
    | exact superpose eq3461 eq11
    | (have j1 := eq3461 X0
       grind)
    | exact resolve eq11 eq3461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3461
  have eq3753 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3615 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3615
    | (have j0 := eq3615 (τ X0)
       grind)
    | exact resolve eq3615 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3615
  have eq3828 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3753 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq3753
    | (have j0 := eq3753 X0
       grind)
    | exact resolve eq3753 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3753
  have eq3837 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3828 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3828
    | (have j0 := eq3828 X0
       grind)
    | exact resolve eq3828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828
  have eq3838 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3837 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq3837
    | (have j0 := eq3837 X0
       grind)
    | exact resolve eq3837 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3837
  have eq3852 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq301 X0
       have i₂ := eq3838 X0
       grind)
    | exact superpose eq3838 eq301
    | (have j0 := eq301 X0
       have j1 := eq3838 X0
       grind)
    | (have r₁ := eq301 X0
       have r₂ := eq3838 X0
       grind)
    | exact resolve eq301 eq3838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq3838
  have eq3896 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3852
  have eq5018 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (τ (k (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3252 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3252
    | exact resolve eq3252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252
  have eq5092 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (τ (k (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq5018 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq5018
    | (have j0 := eq5018 X0
       grind)
    | exact resolve eq5018 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5018
  have eq5101 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5092 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq5092
    | (have j0 := eq5092 X0
       grind)
    | exact resolve eq5092 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5092
  have eq5106 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5101 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5101
    | (have j0 := eq5101 X0
       grind)
    | exact resolve eq5101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101
  have eq5150 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (σ (k (τ X0) (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq5106 (τ X0)
       grind)
    | exact superpose eq5106 eq17
    | (have j1 := eq5106 (τ X0)
       grind)
    | exact resolve eq17 eq5106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106
  have eq5203 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5150 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5150
    | (have j0 := eq5150 X0
       grind)
    | exact resolve eq5150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5150
  have eq5251 : ∀ X0 : G, (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5203 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq5203
    | (have j0 := eq5203 X0
       grind)
    | exact resolve eq5203 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5203
  have eq5293 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5251 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5251
    | (have j0 := eq5251 X0
       grind)
    | exact resolve eq5251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5251
  have eq5538 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq5293 X0
       grind)
    | exact superpose eq5293 eq10
    | (have j1 := eq5293 X0
       grind)
    | exact resolve eq10 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293
  have eq5680 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5538 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5538
    | (have j0 := eq5538 (σ X0)
       grind)
    | exact resolve eq5538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5538
  have eq5755 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5680 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq5680
    | (have j0 := eq5680 X0
       grind)
    | exact resolve eq5680 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq5680
  have eq5768 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5755 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5755
    | (have j0 := eq5755 X0
       grind)
    | exact resolve eq5755 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5755
  have eq5775 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5768 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq5768
    | (have j0 := eq5768 X0
       grind)
    | exact resolve eq5768 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5768
  have eq5778 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq5775 X0
       grind)
    | exact superpose eq5775 eq280
    | (have j0 := eq280 X0
       have j1 := eq5775 X0
       grind)
    | (have r₁ := eq280 X0
       have r₂ := eq5775 X0
       grind)
    | exact resolve eq280 eq5775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5775
  have eq5895 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5778 X0
       have j1 := eq280 X0
       grind)
    | (have r₁ := eq5778 X0
       have r₂ := eq280 X0
       grind)
    | exact resolve eq5778 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq5778
  have eq6048 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5895 (τ X0)
       have i₂ := eq3896 X0
       grind)
    | exact superpose eq3896 eq5895
    | (have j0 := eq5895 (τ X0)
       have j1 := eq3896 X0
       grind)
    | exact resolve eq5895 eq3896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896 eq5895
  have eq6063 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6048 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6048
  have eq6082 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6063 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6063
    | (have j0 := eq6063 X0
       grind)
    | exact resolve eq6063 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6063
  have eq6097 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6082 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq6082 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq6082 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6082
  have eq6140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6097 (σ X0)
       grind)
    | exact superpose eq6097 eq15
    | exact resolve eq15 eq6097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6200 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6140 X0
       have i₂ := eq6097 X0
       grind)
    | exact superpose eq6097 eq6140
    | exact resolve eq6140 eq6097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6097 eq6140
  have eq51568 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq2863 X1 X0
       grind)
    | exact superpose eq2863 eq11
    | (have j1 := eq2863 X1 X0
       grind)
    | exact resolve eq11 eq2863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq51744 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51568 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq51568
    | (have j0 := eq51568 X0 X1
       grind)
    | exact resolve eq51568 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51568
  have eq51799 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51744 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq51744 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq51744 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51744
  have eq51866 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51799 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq51799
    | exact resolve eq51799 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52051 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51799 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51799
  have eq52152 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51866 X0 X1
       have i₂ := eq6200 X0
       grind)
    | exact superpose eq6200 eq51866
    | (have j0 := eq51866 X0 X1
       grind)
    | exact resolve eq51866 eq6200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51866
  have eq52416 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52051 X0 (M.op (M.op X2 X1) X3)
       have i₂ := eq21 X3 X1 X0 X2
       grind)
    | exact superpose eq21 eq52051
    | (have j0 := eq52051 X0 X1
       grind)
    | (have r₁ := eq52051 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq21 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq52051 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq21 X0 X1 X1 X3
       grind)
    | exact resolve eq52051 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52051
  have eq55567 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq52416 X0 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52416
  have eq85662 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52152 x y
       grind)
    | exact superpose eq52152 eq16
    | (have j1 := eq52152 x y
       grind)
    | exact resolve eq16 eq52152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52152
  have eq155325 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq2808 X0 X1
       grind)
    | exact superpose eq2808 eq11
    | (have j1 := eq2808 X0 X1
       grind)
    | exact resolve eq11 eq2808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2808
  have eq155487 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq155325 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq155325
    | (have j0 := eq155325 X0 X1
       grind)
    | exact resolve eq155325 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq155325
  have eq155488 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq155487 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155487
  have eq155641 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq155488 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq155488
    | exact resolve eq155488 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155488
  have eq156240 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X0 X1)) ∨ (k X3 (M.op X0 X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X3 X1 X2 X0
       have i₂ := eq155641 X3 (M.op X0 X1)
       grind)
    | exact superpose eq155641 eq21
    | (have j1 := eq155641 X3 (M.op X0 X1)
       grind)
    | exact resolve eq21 eq155641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156245 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 (M.op X0 X1)) ∨ (k X2 (M.op X0 X1)) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55567 X1 X0 X2
       have i₂ := eq155641 X2 (M.op X0 X1)
       grind)
    | exact superpose eq155641 eq55567
    | (have j1 := eq155641 X2 (M.op X0 X1)
       grind)
    | exact resolve eq55567 eq155641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55567
  have eq173056 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (k X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq156245 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156245
  have eq173057 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq173056 X0 X1
       have j1 := eq156240 X1 X0 x X0
       grind)
    | (have r₁ := eq173056 X1 X0
       have r₂ := eq156240 X0 X1 X1 x
       grind)
    | exact resolve eq173056 eq156240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156240 eq173056
  have eq174112 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq173057 X0 X1
       have i₂ := eq155641 X0 X1
       grind)
    | exact superpose eq155641 eq173057
    | (have j1 := eq155641 X1 X0
       grind)
    | exact resolve eq173057 eq155641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155641 eq173057
  have eq174350 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq174112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174112
  have eq174817 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq174350 X1 (τ X0)
       grind)
    | exact superpose eq174350 eq17
    | exact resolve eq17 eq174350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq174943 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq85662
       have i₂ := eq174350 y x
       grind)
    | exact superpose eq174350 eq85662
    | exact resolve eq85662 eq174350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85662
  have eq174947 : (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq174943
  have eq175062 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174817 X0 X1
       have i₂ := eq174350 (σ X1) X0
       grind)
    | exact superpose eq174350 eq174817
    | exact resolve eq174817 eq174350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174350 eq174817
  have eq179025 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq174947
       grind)
    | exact superpose eq174947 eq10
    | exact resolve eq10 eq174947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179407 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq179025
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq179025
    | exact resolve eq179025 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179025
  have eq182184 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 y X0 x
       have i₂ := eq179407
       grind)
    | exact superpose eq179407 eq21
    | exact resolve eq21 eq179407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179407
  have eq182224 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq182184 X0 x
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq182184
    | exact resolve eq182184 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq182184
  have eq185711 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq175062 X0 y
       have i₂ := eq182224 (τ X0)
       grind)
    | exact superpose eq182224 eq175062
    | exact resolve eq175062 eq182224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182224
  have eq186193 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq185711 X0
       have i₂ := eq175062 X0 x
       grind)
    | exact superpose eq175062 eq185711
    | exact resolve eq185711 eq175062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175062 eq185711
  have eq187600 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq186193 (σ x)
       grind)
    | exact superpose eq186193 eq16
    | exact resolve eq16 eq186193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186193
  have eq187691 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq187600
       have i₂ := eq6200 x
       grind)
    | exact superpose eq6200 eq187600
    | exact resolve eq187600 eq6200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6200 eq187600
  have eq187867 : False := by grind
  exact eq187867

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq281 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X1 X2) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq291 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq399 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq291 X0 X1
       grind)
    | exact superpose eq291 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq291 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq291 X0 X1
       grind)
    | exact resolve eq13 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 X2 X3 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X0) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X3 X0 X1 X2
       have i₂ := eq291 X0 X2
       grind)
    | exact superpose eq291 eq63
    | (have j1 := eq291 X0 X2
       grind)
    | exact resolve eq63 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq291 (σ y) (σ x)
       grind)
    | exact superpose eq291 eq16
    | (have j1 := eq291 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq399 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq411 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq407
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq414 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq410 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq410 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq410 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq417 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq414 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq414
    | exact resolve eq414 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq414 X1 (τ X0)
       grind)
    | exact superpose eq414 eq17
    | (have j1 := eq414 X1 (τ X0)
       grind)
    | exact resolve eq17 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq445 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq414 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq1019 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq439 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq439
    | exact resolve eq439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq1064 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1019 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1019
    | (have j0 := eq1019 X0 X1
       grind)
    | exact resolve eq1019 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1828 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq417 X1 X0
       grind)
    | exact superpose eq417 eq10
    | (have j1 := eq417 X1 X0
       grind)
    | exact resolve eq10 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq1865 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1828 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1828
    | (have j0 := eq1828 X0 X1
       grind)
    | exact resolve eq1828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1906 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1865 y x
       grind)
    | exact superpose eq1865 eq16
    | (have j1 := eq1865 y x
       grind)
    | exact resolve eq16 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq1944 : y = (k x y) := by
    first
    | (have j1 := eq1064 x y
       grind)
    | (have r₁ := eq1906
       have r₂ := eq1064 x y
       grind)
    | exact resolve eq1906 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq1906
  have eq1963 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op X0 (M.op y X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq283 y X0 x
       have i₂ := eq1944
       grind)
    | exact superpose eq1944 eq283
    | (have j0 := eq283 y X0 x
       grind)
    | exact resolve eq283 eq1944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq1964 : ∀ X0 X1 : G, y = (M.op x y) ∨ (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq401 y X0 x X1
       have i₂ := eq1944
       grind)
    | exact superpose eq1944 eq401
    | (have j0 := eq401 y X0 x X1
       grind)
    | exact resolve eq401 eq1944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq1966 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 (M.op y X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1963 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963
  have eq1974 : ∀ X0 X1 X2 X3 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) ∨ (M.op X2 y) = (M.op X2 (M.op y X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X1 y X0 x
       have i₂ := eq1964 X2 X3
       grind)
    | exact superpose eq1964 eq63
    | (have j1 := eq1964 X0 X1
       grind)
    | exact resolve eq63 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1964
  have eq1997 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op X0 (M.op y X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq411
       have i₂ := eq1966 X0
       grind)
    | exact superpose eq1966 eq411
    | (have j1 := eq1966 X0
       grind)
    | exact resolve eq411 eq1966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2008 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op X0 (M.op y X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1997 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997
  have eq2009 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op y X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2008 X0
       have i₂ := eq1944
       grind)
    | exact superpose eq1944 eq2008
    | (have j0 := eq2008 X0
       grind)
    | exact resolve eq2008 eq1944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq3784 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op X0 (M.op y X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2009 X0
       grind)
    | exact superpose eq2009 eq16
    | (have j1 := eq2009 X0
       grind)
    | exact resolve eq16 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009
  have eq3816 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (M.op y X0)) = (M.op X0 x) ∨ (M.op X1 (M.op y X1)) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq3784 X0
       have i₂ := eq1966 X1
       grind)
    | exact superpose eq1966 eq3784
    | (have j0 := eq3784 X0
       have j1 := eq1966 X0
       grind)
    | exact resolve eq3784 eq1966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966 eq3784
  have eq3824 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op X0 x) ∨ (M.op X1 (M.op y X1)) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have j0 := eq3816 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816
  have eq6914 : ∀ X0 X1 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1974 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq6915 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6914 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6914
  have eq11465 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 (M.op y X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3824 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3824
  have eq11466 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq11465 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11465
  have eq11467 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq11466 X0
       have i₂ := eq6915 X0 X0
       grind)
    | exact superpose eq6915 eq11466
    | exact resolve eq11466 eq6915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6915 eq11466
  have eq11554 : ∀ X0 : G, y = (M.op X0 x) ∨ (M.op X0 x) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq291 y X0
       have i₂ := eq11467 X0
       grind)
    | exact superpose eq11467 eq291
    | exact resolve eq291 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq11557 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq445 X0 y
       have i₂ := eq11467 X0
       grind)
    | exact superpose eq11467 eq445
    | (have j0 := eq445 X0 y
       grind)
    | exact resolve eq445 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq11592 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq411
       have i₂ := eq11467 x
       grind)
    | exact superpose eq11467 eq411
    | exact resolve eq411 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq11626 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11592
       have i₂ := eq1944
       grind)
    | exact superpose eq1944 eq11592
    | exact resolve eq11592 eq1944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11592
  have eq12011 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ (M.op X0 x) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq11557 X0
       have i₂ := eq11554 X0
       grind)
    | exact superpose eq11554 eq11557
    | (have j0 := eq11557 X0
       have j1 := eq11554 X0
       grind)
    | (have r₁ := eq11557 X0
       have r₂ := eq11554 X0
       grind)
    | exact resolve eq11557 eq11554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11557
  have eq12074 : ∀ X0 : G, y = (k X0 y) ∨ (M.op X0 x) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq12011 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12011
  have eq12159 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ (M.op X0 x) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq12074 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12074
  have eq12162 : ∀ X0 : G, (M.op X0 x) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq12159 X0
       have j1 := eq11554 X0
       grind)
    | (have r₁ := eq12159 X0
       have r₂ := eq11554 X0
       grind)
    | exact resolve eq12159 eq11554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11554 eq12159
  have eq12272 : y = (M.op x x) := by
    first
    | (have i₁ := eq1944
       have i₂ := eq12162 x
       grind)
    | exact superpose eq12162 eq1944
    | exact resolve eq1944 eq12162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944 eq12162
  have eq16744 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11626
       have i₂ := eq12272
       grind)
    | exact superpose eq12272 eq11626
    | exact resolve eq11626 eq12272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11626
  have eq16749 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16744
  have eq16756 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16749
       grind)
    | exact superpose eq16749 eq16
    | exact resolve eq16 eq16749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16749
  have eq16796 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16756
       have i₂ := eq11467 x
       grind)
    | exact superpose eq11467 eq16756
    | exact resolve eq16756 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11467 eq16756
  have eq16804 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq16796
       have i₂ := eq12272
       grind)
    | exact superpose eq12272 eq16796
    | exact resolve eq16796 eq12272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12272 eq16796
  have eq16805 : False := by grind
  exact eq16805

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq61 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k X1 (σ X0))
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq294 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99 x y
       grind)
    | exact superpose eq99 eq16
    | (have j1 := eq99 x y
       grind)
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1598 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq294
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq294
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq294
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq294
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq294 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1599 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1598
  have eq1774 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq302 (τ X0) (τ X1)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq302
    | (have j0 := eq302 (τ X0) (τ X1)
       grind)
    | exact resolve eq302 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq302
  have eq1805 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1774 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq1774
    | (have j0 := eq1774 X0 X1
       grind)
    | exact resolve eq1774 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774
  have eq1819 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1805 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1805
    | (have j0 := eq1805 X0 X1
       grind)
    | exact resolve eq1805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq1828 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1819 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1819
    | (have j0 := eq1819 X0 X1
       grind)
    | exact resolve eq1819 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq1832 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1828 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1828
    | (have j0 := eq1828 X0 X1
       grind)
    | exact resolve eq1828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1835 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1832 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq1832
    | (have j0 := eq1832 X0 X1
       grind)
    | exact resolve eq1832 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1832
  have eq1837 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1835 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1835
    | (have j0 := eq1835 X0 X1
       grind)
    | exact resolve eq1835 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1838 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1837 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1837
    | (have j0 := eq1837 X0 X1
       grind)
    | exact resolve eq1837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837
  have eq22969 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1599
       grind)
    | exact superpose eq1599 eq16
    | exact resolve eq16 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq22970 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq22969
       have r₂ := eq22 x
       grind)
    | exact resolve eq22969 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22969
  have eq22974 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61 y (σ x)
       have i₂ := eq22970
       grind)
    | exact superpose eq22970 eq61
    | (have j0 := eq61 y (σ x)
       grind)
    | (have r₁ := eq61 y (σ x)
       have r₂ := eq22970
       grind)
    | exact resolve eq61 eq22970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq22970
  have eq22992 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq22974
  have eq22993 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq22992
  have eq23000 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq22993
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22993
    | exact resolve eq22993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22993
  have eq23320 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23000
       grind)
    | exact superpose eq23000 eq10
    | exact resolve eq10 eq23000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23000
  have eq23400 : x = y ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq23320
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23320
    | exact resolve eq23320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23320
  have eq23402 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23400
       grind)
    | exact superpose eq23400 eq16
    | exact resolve eq16 eq23400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23400
  have eq23403 : (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq23402
       have r₂ := eq22 x
       grind)
    | exact resolve eq23402 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23402
  have eq23704 : (k x y) = (τ (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq23403
       grind)
    | exact superpose eq23403 eq10
    | exact resolve eq10 eq23403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23403
  have eq23790 : (k x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq23704
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq23704
    | exact resolve eq23704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23704
  have eq23798 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1838 x y
       have i₂ := eq23790
       grind)
    | exact superpose eq23790 eq1838
    | (have j0 := eq1838 x y
       grind)
    | (have r₁ := eq1838 x y
       have r₂ := eq23790
       grind)
    | exact resolve eq1838 eq23790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838 eq23790
  have eq23807 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq23798
  have eq23808 : x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq23807
  have eq24123 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23808
       grind)
    | exact superpose eq23808 eq16
    | exact resolve eq16 eq23808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23808
  have eq24124 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq24123
       have r₂ := eq22 x
       grind)
    | exact resolve eq24123 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24123
  have eq24125 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq24124
       grind)
    | exact superpose eq24124 eq13
    | (have j0 := eq13 (M.op x y) (k X0 y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq24124
       grind)
    | exact resolve eq13 eq24124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27331 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have j0 := eq24125 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24125
  have eq27335 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq294
       have i₂ := eq27331
       grind)
    | exact superpose eq27331 eq294
    | exact resolve eq294 eq27331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq27331
  have eq27343 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27335
  have eq27348 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27343
       have i₂ := eq24124
       grind)
    | exact superpose eq24124 eq27343
    | exact resolve eq27343 eq24124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24124 eq27343
  have eq27350 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq27348
       have r₂ := eq16
       grind)
    | exact resolve eq27348 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27348
  have eq27546 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27350
       grind)
    | exact superpose eq27350 eq16
    | exact resolve eq16 eq27350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27350
  have eq27554 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq27546
       have r₂ := eq22 x
       grind)
    | exact resolve eq27546 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27546
  have eq27555 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27554
       grind)
    | exact superpose eq27554 eq16
    | exact resolve eq16 eq27554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27556 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27554
       grind)
    | exact superpose eq27554 eq10
    | exact resolve eq10 eq27554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27554
  have eq27652 : x = y := by
    first
    | (have i₁ := eq27556
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27556
    | exact resolve eq27556 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27556
  have eq27653 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq27555
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq27555
    | exact resolve eq27555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq27555
  have eq27658 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq27653
       have i₂ := eq27652
       grind)
    | exact superpose eq27652 eq27653
    | exact resolve eq27653 eq27652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27652 eq27653
  have eq27659 : False := by grind
  exact eq27659

/-- `Equation366`: `x ◇ x = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_y_x_pyx_Equation366 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law366 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law366.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X2) := by
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
  have eq37 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 (M.op x X0) X3
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (M.op y y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0 x
       have i₂ := eq14 X1 X1 x
       grind)
    | exact superpose eq14 eq37
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq47 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq48 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq49 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : y ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq38 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op y y) (M.op x y)
       have r₂ := eq38 (M.op y y)
       grind)
    | exact resolve eq13 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq39 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (M.op (σ y) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq39 (M.op (σ y) (σ y))
       grind)
    | exact resolve eq13 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq47
    | (have j0 := eq47 (M.op x y)
       grind)
    | exact resolve eq47 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X0 X0) = X2 ∨ (k X2 (M.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (M.op y y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op y y) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq38 eq12
    | (have j0 := eq12 X0 (M.op x y)
       grind)
    | exact resolve eq12 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = X2 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq41 X1 X0
       grind)
    | (have i₁ := eq12 X2 X1
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq41 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq41 X0 X0
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq102 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq102 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq102 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq111 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq93 X0
       grind)
    | (have r₁ := eq93 X0
       have r₂ := eq41 y (M.op x y)
       grind)
    | (have r₁ := eq93 X0
       have r₂ := eq41 (M.op x y) y
       grind)
    | exact resolve eq93 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq112 : ∀ X0 X1 X2 : G, (k X2 (M.op X1 X0)) = X2 ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq91 X0 X1 X2
       grind)
    | (have r₁ := eq91 X0 X1 X2
       have r₂ := eq14 X0 X1 (M.op X1 X0)
       grind)
    | exact resolve eq91 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq123 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq132 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq48
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq48 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq149 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq142
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq142
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (σ (k (k y x) X0)) = (k (k (σ y) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k y x) X0
       have i₂ := eq142
       grind)
    | exact superpose eq142 eq10
    | exact resolve eq10 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq142
       grind)
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq149
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq149
    | exact resolve eq149 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq156 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq155
    | exact resolve eq155 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq157 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq156
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq156
    | exact resolve eq156 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq158 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq157
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq157
    | exact resolve eq157 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq177 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq49 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49
    | (have j0 := eq49 x
       grind)
    | exact resolve eq49 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq242 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq53
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq53 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq16
    | exact resolve eq16 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq507 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op x y) = (k X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X1
       have i₂ := eq41 y X0
       grind)
    | (have i₁ := eq81 X1
       have i₂ := eq41 X0 y
       grind)
    | exact superpose eq41 eq81
    | (have j0 := eq81 X1
       grind)
    | (have r₁ := eq81 (M.op X1 X1)
       have r₂ := eq41 y X1
       grind)
    | (have r₁ := eq81 (M.op X0 X0)
       have r₂ := eq41 X0 y
       grind)
    | exact resolve eq81 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : (M.op x y) = (k (M.op y y) (M.op x y)) := by
    first
    | (have j0 := eq81 (M.op y y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq560 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq83 (M.op (σ y) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq686 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq92
       have i₂ := eq41 x X0
       grind)
    | (have i₁ := eq92
       have i₂ := eq41 X0 x
       grind)
    | exact superpose eq41 eq92
    | exact resolve eq92 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq94
       have i₂ := eq41 sF2 x
       grind)
    | (have i₁ := eq94
       have i₂ := eq41 X0 sF2
       grind)
    | exact superpose eq41 eq94
    | exact resolve eq94 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq714 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq111 eq46
    | (have j1 := eq111 (τ X0)
       grind)
    | exact resolve eq46 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq717 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq20 eq714
    | (have j0 := eq714 X0
       grind)
    | exact resolve eq714 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq724 : ∀ X0 : G, (τ X0) = (M.op y y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq717 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq717
    | (have j0 := eq717 X0
       grind)
    | exact resolve eq717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq752 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq303
    | (have j0 := eq303 X0 (M.op x y)
       grind)
    | exact resolve eq303 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq836 : (k (k y x) (M.op x y)) = (τ (k (k (σ y) (σ x)) (σ (M.op x y)))) := by
    first
    | exact superpose eq154 eq752
    | exact resolve eq752 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1050 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq123 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1493 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq724 X1
       have i₂ := eq41 y X0
       grind)
    | (have i₁ := eq724 X1
       have i₂ := eq41 X0 y
       grind)
    | exact superpose eq41 eq724
    | (have j0 := eq724 X1
       grind)
    | exact resolve eq724 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1495 : ∀ X0 : G, (σ (M.op y y)) = X0 ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq15 X0
       have i₂ := eq724 X0
       grind)
    | exact superpose eq724 eq15
    | (have j1 := eq724 X0
       grind)
    | exact resolve eq15 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1517 : ∀ X0 : G, (M.op x y) = (k (τ X0) (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq509
       have i₂ := eq724 X0
       grind)
    | exact superpose eq724 eq509
    | (have j1 := eq724 X0
       grind)
    | exact resolve eq509 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq1550 : ∀ X0 : G, (M.op x y) = (τ (k X0 (σ (M.op x y)))) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq752 eq1517
    | (have j0 := eq1517 X0
       grind)
    | exact resolve eq1517 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1683 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1
       have i₂ := eq1493 X0 X1
       grind)
    | exact superpose eq1493 eq15
    | (have j1 := eq1493 X0 X1
       grind)
    | exact resolve eq15 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1747 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (k (M.op y y) (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 (M.op y y)
       have i₂ := eq1495 X0
       grind)
    | (have i₁ := eq53 X0
       have i₂ := eq1495 (σ X0)
       grind)
    | exact superpose eq1495 eq53
    | (have j1 := eq1495 X0
       grind)
    | exact resolve eq53 eq1495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495
  have eq1752 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq509 eq1747
    | (have j0 := eq1747 X0
       grind)
    | exact resolve eq1747 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq1747
  have eq1755 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq1752
    | (have j0 := eq1752 X0
       grind)
    | exact resolve eq1752 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq1766 : ∀ X0 : G, (σ (M.op x y)) ≠ X0 ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq1755 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq1906 : ∀ X0 : G, (M.op x y) = (τ (σ (k X0 (M.op x y)))) ∨ (σ X0) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53 eq1550
    | exact resolve eq1550 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq1944 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op x y))) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1906 X0
       have i₂ := eq16 (k X0 sF0)
       grind)
    | exact superpose eq16 eq1906
    | (have j0 := eq1906 X0
       grind)
    | exact resolve eq1906 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906
  have eq7697 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 (M.op x y))) ∨ (σ (M.op x y)) = (k (σ X0) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq242 eq13
    | (have j0 := eq13 (σ X0) (σ (M.op x y))
       have j1 := eq242 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ (M.op x y))
       have r₂ := eq242 X0
       grind)
    | exact resolve eq13 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq7737 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 (M.op x y))) ∨ (σ (M.op x y)) = (k (σ X0) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq7697 X0
       have j1 := eq13 (σ X0) (σ (M.op x y))
       grind)
    | (have r₁ := eq7697 X0
       have r₂ := eq13 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq7697 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7697
  have eq7761 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 (M.op x y))) ∨ (σ (M.op x y)) = (σ (k X0 (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq53 eq7737
    | (have j0 := eq7737 X0
       grind)
    | exact resolve eq7737 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7737
  have eq8271 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq145 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq145
    | (have j0 := eq145 x
       grind)
    | exact resolve eq145 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq8342 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8271
    | exact resolve eq8271 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8271
  have eq8355 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8342
       have i₂ := eq142
       grind)
    | exact superpose eq142 eq8342
    | exact resolve eq8342 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8342
  have eq8359 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8355
    | exact resolve eq8355 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8355
  have eq8361 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq8359
    | exact resolve eq8359 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8359
  have eq8490 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op x y)) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1944 eq16
    | (have j1 := eq1944 X0
       grind)
    | exact resolve eq16 eq1944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq8530 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8490 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq8490
    | (have j0 := eq8490 X0
       grind)
    | exact resolve eq8490 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8490
  have eq8610 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq8530 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8530
  have eq9985 : ∀ X0 : G, (σ X0) ≠ (M.op (k (σ x) (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) ∨ (σ (k X0 (k x (M.op x y)))) = (M.op (k (σ x) (σ (M.op x y))) (σ X0)) ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq87 eq1050
    | exact resolve eq1050 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq1050
  have eq16786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq158 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16786
    | exact resolve eq16786 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16786
  have eq16798 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16787
       have r₂ := eq27
       grind)
    | exact resolve eq16787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16787
  have eq16802 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16798
    | exact resolve eq16798 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq16804 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16802
    | exact resolve eq16802 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16802
  have eq16821 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16804 eq704
    | (have r₁ := eq704 (σ x)
       have r₂ := eq16804
       grind)
    | exact resolve eq704 eq16804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq16804
  have eq16861 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq16821
  have eq16862 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq16861
  have eq17513 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16862 eq154
    | exact resolve eq154 eq16862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16862
  have eq17534 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17513
    | exact resolve eq17513 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17513
  have eq17542 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17534
       have r₂ := eq92
       grind)
    | exact resolve eq17534 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq17534
  have eq17545 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq142
       have i₂ := eq17542
       grind)
    | exact superpose eq17542 eq142
    | exact resolve eq142 eq17542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17552 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq17542
       grind)
    | exact superpose eq17542 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq17542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17542
  have eq17553 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17552
  have eq17555 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17553
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17553
    | exact resolve eq17553 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17553
  have eq17556 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17555
  have eq17563 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17545
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17545
    | exact resolve eq17545 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17545
  have eq17566 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17556
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17556
    | exact resolve eq17556 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17556
  have eq17582 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17563 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq17563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17563
  have eq17583 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17582
  have eq17587 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17583
    | exact resolve eq17583 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17583
  have eq17588 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq17587
  have eq17600 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17588
    | exact resolve eq17588 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17588
  have eq17717 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17566
       have i₂ := eq41 x X0
       grind)
    | (have i₁ := eq17566
       have i₂ := eq41 X0 x
       grind)
    | exact superpose eq41 eq17566
    | exact resolve eq17566 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17725 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq507 x X0
       have i₂ := eq17566
       grind)
    | exact superpose eq17566 eq507
    | (have j0 := eq507 X0 X0
       grind)
    | (have r₁ := eq507 x (M.op x y)
       have r₂ := eq17566
       grind)
    | exact resolve eq507 eq17566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17736 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1683 x X0
       have i₂ := eq17566
       grind)
    | exact superpose eq17566 eq1683
    | (have j0 := eq1683 X0 X0
       grind)
    | exact resolve eq1683 eq17566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17747 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq112 x x x
       have i₂ := eq17566
       grind)
    | exact superpose eq17566 eq112
    | (have j0 := eq112 y x X0
       grind)
    | exact resolve eq112 eq17566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17566
  have eq17794 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17747 X0
       have j1 := eq8610 X0
       grind)
    | (have r₁ := eq17747 (M.op x y)
       have r₂ := eq8610 (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq17747 X0
       have r₂ := eq8610 X0
       grind)
    | (have r₁ := eq17747 (M.op x y)
       have r₂ := eq8610 (M.op x y)
       grind)
    | exact resolve eq17747 eq8610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17747
  have eq17802 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq17736
    | (have j0 := eq17736 X0
       grind)
    | exact resolve eq17736 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17736
  have eq17807 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17802 X0
       have j1 := eq1766 X0
       grind)
    | (have r₁ := eq17802 X0
       have r₂ := eq1766 X0
       grind)
    | (have r₁ := eq17802 (σ (M.op x y))
       have r₂ := eq1766 (σ (M.op x y))
       grind)
    | (have r₁ := eq17802 (σ (M.op x y))
       have r₂ := eq1766 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq17802 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq18161 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17600
       have i₂ := eq17717 sF2
       grind)
    | exact superpose eq17717 eq17600
    | exact resolve eq17600 eq17717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17600 eq17717
  have eq18169 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18161
  have eq18235 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18169 eq27
    | exact resolve eq27 eq18169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18237 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18169 eq82
    | (have r₁ := eq82
       have r₂ := eq18169
       grind)
    | exact resolve eq82 eq18169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18169
  have eq18275 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18237
  have eq18308 : ∀ X0 : G, (τ X0) = (τ (k X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq752 eq17794
    | exact resolve eq17794 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq18669 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f18669_14 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
      intro X0 X1
      grind
    have f18669_15 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f18669_22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
      intro X0
      grind
    have f18669_24 : (σ (τ X0)) ≠ (k X0 (σ (σ (M.op x y)))) := by grind
    have f18669_25 : y ≠ (M.op x y) := by grind
    have f18669_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f18669_27 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f18669_15 X0
         grind)
      | (have r₁ := f18669_15 X0
         have r₂ := f18669_25
         grind)
      | exact resolve f18669_15 f18669_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f18669_28 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
      intro X0
      first
      | (have j0 := f18669_27 X0
         grind)
      | (have r₁ := f18669_27 X0
         have r₂ := f18669_26
         grind)
      | exact resolve f18669_27 f18669_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f18669_50 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op x y)))) := by
      intro X0
      first
      | (have i₁ := f18669_14 X0 (σ (M.op x y))
         have i₂ := f18669_28 (τ X0)
         grind)
      | exact superpose f18669_28 f18669_14
      | exact resolve f18669_14 f18669_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f18669_52 : ∀ X0 : G, (k X0 (σ (σ (M.op x y)))) = X0 := by
      intro X0
      first
      | (have i₁ := f18669_50 X0
         have i₂ := f18669_22 X0
         grind)
      | exact superpose f18669_22 f18669_50
      | exact resolve f18669_50 f18669_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f18669_109 : X0 ≠ (σ (τ X0)) := by
      first
      | (have i₁ := f18669_24
         have i₂ := f18669_52 X0
         grind)
      | exact superpose f18669_52 f18669_24
      | exact resolve f18669_24 f18669_52
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f18669_110 : False := by
      first
      | (have r₁ := f18669_109
         have r₂ := f18669_22 X0
         grind)
      | exact resolve f18669_109 f18669_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f18669_110
  have eq18697 : ∀ X0 : G, (k X0 (σ (σ (M.op x y)))) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18669 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq18669
    | exact resolve eq18669 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18669
  have eq18979 : (τ (σ x)) = (k y x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18275 eq154
    | exact resolve eq154 eq18275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18980 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18275 eq158
    | exact resolve eq158 eq18275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq18275
  have eq18992 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq18980
  have eq19003 : x = (k y x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq18979
    | exact resolve eq18979 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18979
  have eq19010 : x = (k y x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19003
       have r₂ := eq80
       grind)
    | exact resolve eq19003 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19003
  have eq19016 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq142
       have i₂ := eq19010
       grind)
    | exact superpose eq19010 eq142
    | exact resolve eq142 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19024 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq19010
       grind)
    | exact superpose eq19010 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19010
  have eq19025 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19024
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19024
    | exact resolve eq19024 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19024
  have eq19032 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19016
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19016
    | exact resolve eq19016 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19016
  have eq19034 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19025
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19025
    | exact resolve eq19025 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19025
  have eq19038 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19034
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19034
    | exact resolve eq19034 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19034
  have eq19046 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k y x) X0)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19032 eq153
    | exact resolve eq153 eq19032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq19066 : ∀ X0 : G, (σ (k x X0)) = (σ (k (k y x) X0)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq47 eq19046
    | exact resolve eq19046 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq19046
  have eq19314 : (σ (M.op x y)) = (σ (k (M.op x y) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49 eq18697
    | exact resolve eq18697 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq18697
  have eq20075 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (M.op x y) (σ (M.op x y))) (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19314 eq53
    | exact resolve eq53 eq19314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq19314
  have eq20133 : (σ (M.op x y)) = (σ (k (k (M.op x y) (σ (M.op x y))) (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20075
       have i₂ := eq106 sF1
       grind)
    | exact superpose eq106 eq20075
    | exact resolve eq20075 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20075
  have eq31448 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq686 x
       have i₂ := eq18992
       grind)
    | exact superpose eq18992 eq686
    | (have r₁ := eq686 x
       have r₂ := eq18992
       grind)
    | exact resolve eq686 eq18992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18992
  have eq31512 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq31448
  have eq31513 : y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq31512
  have eq32060 : (τ (σ (M.op x y))) = (k (k (M.op x y) (σ (M.op x y))) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20133 eq16
    | exact resolve eq16 eq20133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20133
  have eq32145 : (M.op x y) = (k (k (M.op x y) (σ (M.op x y))) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq32060
    | exact resolve eq32060 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32060
  have eq32155 : (M.op x y) = (k (M.op (σ (M.op x y)) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq32145
       have i₂ := eq11 sF0 sF1
       grind)
    | exact superpose eq11 eq32145
    | (have j1 := eq11 (M.op x y) (σ (M.op x y))
       grind)
    | exact resolve eq32145 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32145
  have eq32186 : (M.op x y) = (k (M.op (σ (M.op x y)) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have j1 := eq17725 (M.op (σ (M.op x y)) (M.op x y))
       grind)
    | (have r₁ := eq32155
       have r₂ := eq17725 (k (M.op (σ (M.op x y)) (M.op x y)) (M.op x y))
       grind)
    | (have r₁ := eq32155
       have r₂ := eq17725 y
       grind)
    | (have r₁ := eq32155
       have r₂ := eq17725 (M.op (σ (M.op x y)) (M.op x y))
       grind)
    | exact resolve eq32155 eq17725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17725 eq32155
  have eq32188 : (M.op x y) = (k (M.op (σ (M.op x y)) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq507 x (M.op (σ (M.op x y)) (M.op x y))
       grind)
    | (have r₁ := eq32186
       have r₂ := eq507 (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))
       grind)
    | exact resolve eq32186 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq32186
  have eq32205 : (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32188 eq17794
    | exact resolve eq17794 eq32188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17794 eq32188
  have eq32212 : (M.op x y) = (M.op (σ (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32205
  have eq32231 : (M.op x y) ≠ (M.op x y) ∨ (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32212 eq13
    | (have j0 := eq13 (M.op x y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (M.op x y) (σ (M.op x y))
       have r₂ := eq32212
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq32212
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq32212
       grind)
    | exact resolve eq13 eq32212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32212
  have eq32277 : (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32231
  have eq32316 : (τ (σ (M.op x y))) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32277 eq18308
    | exact resolve eq18308 eq32277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18308
  have eq32317 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32277 eq17807
    | exact resolve eq17807 eq32277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17807 eq32277
  have eq32320 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq32317
  have eq32321 : (τ (σ (M.op x y))) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32316
  have eq32327 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq32321
    | exact resolve eq32321 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32321
  have eq32330 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq32320 eq39
    | exact resolve eq39 eq32320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32331 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32320 eq82
    | (have r₁ := eq82
       have r₂ := eq32320
       grind)
    | exact resolve eq82 eq32320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32333 : (σ y) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32320 eq560
    | exact resolve eq560 eq32320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq32370 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq32331
  have eq32587 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32370 eq154
    | exact resolve eq154 eq32370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32370
  have eq32619 : x = (k y x) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq28 eq32587
    | exact resolve eq32587 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32587
  have eq32626 : x = (k y x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq32619
       have r₂ := eq80
       grind)
    | exact resolve eq32619 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32619
  have eq32632 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq142
       have i₂ := eq32626
       grind)
    | exact superpose eq32626 eq142
    | exact resolve eq142 eq32626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32626
  have eq32657 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32632
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32632
    | exact resolve eq32632 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32632
  have eq32678 : (τ (k (σ x) (σ (M.op x y)))) = (k (k y x) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32657 eq836
    | exact resolve eq836 eq32657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq32657
  have eq32691 : (k x (M.op x y)) = (k (k y x) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq132 eq32678
    | exact resolve eq32678 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq32678
  have eq33926 : ∀ X0 : G, (σ y) = (k (M.op (σ y) X0) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq32330 eq32333
    | exact resolve eq32333 eq32330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32330 eq32333
  have eq33949 : ∀ X0 : G, (σ y) = (k (M.op (σ y) X0) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq33926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33926
  have eq38402 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19038
       have i₂ := eq41 x X0
       grind)
    | (have i₁ := eq19038
       have i₂ := eq41 X0 x
       grind)
    | exact superpose eq41 eq19038
    | exact resolve eq19038 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38417 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq686 x
       have i₂ := eq19038
       grind)
    | exact superpose eq19038 eq686
    | (have r₁ := eq686 x
       have r₂ := eq19038
       grind)
    | exact resolve eq686 eq19038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19038
  have eq38492 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq38417
  have eq38493 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq38492
  have eq43580 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq142
       have i₂ := eq31513
       grind)
    | exact superpose eq31513 eq142
    | exact resolve eq142 eq31513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31513
  have eq43638 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43580
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43580
    | exact resolve eq43580 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43580
  have eq48311 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq142
       have i₂ := eq38493
       grind)
    | exact superpose eq38493 eq142
    | exact resolve eq142 eq38493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38493
  have eq48373 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq48311
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48311
    | exact resolve eq48311 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48311
  have eq53494 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43638 eq19032
    | exact resolve eq19032 eq43638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43638
  have eq53522 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq53494
  have eq53554 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq53522 eq26
    | exact resolve eq26 eq53522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53522
  have eq57639 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48373 eq19032
    | exact resolve eq19032 eq48373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19032 eq48373
  have eq57675 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq57639
  have eq57795 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57675 eq18235
    | exact resolve eq18235 eq57675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18235 eq57675
  have eq57967 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq57795
  have eq62292 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq53554 eq38402
    | exact resolve eq38402 eq53554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38402 eq53554
  have eq62362 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq62292
  have eq62410 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq62362
       have r₂ := eq57967
       grind)
    | exact resolve eq62362 eq57967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57967 eq62362
  have eq63192 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62410 eq27
    | exact resolve eq27 eq62410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63258 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62410 eq32320
    | exact resolve eq32320 eq62410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32320 eq62410
  have eq63273 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq63258
  have eq73025 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq63273
       have r₂ := eq63192
       grind)
    | exact resolve eq63273 eq63192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63273
  have eq73029 : y = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73025 eq29
    | exact resolve eq29 eq73025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq73025
  have eq73884 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73029 eq32327
    | exact resolve eq32327 eq73029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32327
  have eq73967 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq73884
  have eq73989 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73967 eq27
    | exact resolve eq27 eq73967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73991 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73967 eq82
    | (have r₁ := eq82
       have r₂ := eq73967
       grind)
    | exact resolve eq82 eq73967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq73967
  have eq74048 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq73991
  have eq75060 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74048 eq154
    | exact resolve eq154 eq74048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq74048
  have eq75110 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq75060
    | exact resolve eq75060 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75060
  have eq75117 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq75110
       have r₂ := eq80
       grind)
    | exact resolve eq75110 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq75110
  have eq75125 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142
       have i₂ := eq75117
       grind)
    | exact superpose eq75117 eq142
    | exact resolve eq142 eq75117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75148 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq75117
       grind)
    | exact superpose eq75117 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq75117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75117
  have eq75151 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75148
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75148
    | exact resolve eq75148 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75148
  have eq75152 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq75151
  have eq75161 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75125
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq75125
    | exact resolve eq75125 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75125
  have eq75164 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75152
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75152
    | exact resolve eq75152 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75152
  have eq75168 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75164
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75164
    | exact resolve eq75164 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75164
  have eq76867 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq686 x
       have i₂ := eq75168
       grind)
    | exact superpose eq75168 eq686
    | (have r₁ := eq686 x
       have r₂ := eq75168
       grind)
    | exact resolve eq686 eq75168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq76875 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1683 x X0
       have i₂ := eq75168
       grind)
    | exact superpose eq75168 eq1683
    | (have j0 := eq1683 X0 X0
       grind)
    | exact resolve eq1683 eq75168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76898 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq112 x x x
       have i₂ := eq75168
       grind)
    | exact superpose eq75168 eq112
    | (have j0 := eq112 y x X0
       grind)
    | exact resolve eq112 eq75168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq75168
  have eq76970 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq76867
  have eq76971 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq76970
  have eq77017 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq76898 X0
       have j1 := eq8610 X0
       grind)
    | (have r₁ := eq76898 (M.op x y)
       have r₂ := eq8610 (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq76898 X0
       have r₂ := eq8610 X0
       grind)
    | (have r₁ := eq76898 (M.op x y)
       have r₂ := eq8610 (M.op x y)
       grind)
    | exact resolve eq76898 eq8610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8610 eq76898
  have eq77030 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq76875
    | (have j0 := eq76875 X0
       grind)
    | exact resolve eq76875 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76875
  have eq77039 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq77030 X0
       have j1 := eq1766 X0
       grind)
    | (have r₁ := eq77030 X0
       have r₂ := eq1766 X0
       grind)
    | (have r₁ := eq77030 (σ (M.op x y))
       have r₂ := eq1766 (σ (M.op x y))
       grind)
    | (have r₁ := eq77030 (σ (M.op x y))
       have r₂ := eq1766 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq77030 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77030
  have eq78537 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142
       have i₂ := eq76971
       grind)
    | exact superpose eq76971 eq142
    | exact resolve eq142 eq76971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78559 : (k x (M.op x y)) = (k y (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32691
       have i₂ := eq76971
       grind)
    | exact superpose eq76971 eq32691
    | exact resolve eq32691 eq76971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32691 eq76971
  have eq78588 : (k x (M.op x y)) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq78559
       have r₂ := eq63192
       grind)
    | exact resolve eq78559 eq63192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78559
  have eq78599 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78537
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq78537
    | exact resolve eq78537 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78537
  have eq83835 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq77017 eq375
    | exact resolve eq375 eq77017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83925 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq83835 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq83835
    | exact resolve eq83835 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83835
  have eq88259 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78599 eq75161
    | exact resolve eq75161 eq78599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78599
  have eq88266 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq88259
  have eq88867 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq88266 eq73989
    | exact resolve eq73989 eq88266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88892 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq88867
  have eq101960 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73029 eq83925
    | exact resolve eq83925 eq73029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73029 eq83925
  have eq102132 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq101960 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101960
  have eq102405 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq46 X0 y
       have i₂ := eq102132 (τ X0)
       grind)
    | exact superpose eq102132 eq46
    | exact resolve eq46 eq102132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq102132
  have eq102539 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq102405 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq102405
    | (have j0 := eq102405 X0
       grind)
    | exact resolve eq102405 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102405
  have eq102643 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq102539 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq102539
    | exact resolve eq102539 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102539
  have eq102779 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq102643 eq33949
    | exact resolve eq33949 eq102643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33949 eq102643
  have eq102932 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq102779 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102779
  have eq103044 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq102932 X0
       grind)
    | (have r₁ := eq102932 X0
       have r₂ := eq63192
       grind)
    | exact resolve eq102932 eq63192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63192 eq102932
  have eq104140 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq88266 eq103044
    | exact resolve eq103044 eq88266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103044
  have eq104387 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq104140 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104140
  have eq109185 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq104387 sF2
       have i₂ := eq41 sF2 x
       grind)
    | (have i₁ := eq104387 sF2
       have i₂ := eq41 X0 sF2
       grind)
    | exact superpose eq41 eq104387
    | exact resolve eq104387 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104387
  have eq192780 : y = (k x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78588 eq77017
    | exact resolve eq77017 eq78588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77017 eq78588
  have eq192784 : y = (k x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq192780
  have eq230269 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq192784 eq7761
    | (have j0 := eq7761 x
       grind)
    | exact resolve eq7761 eq192784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7761 eq192784
  have eq230430 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq230269
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq230269
    | exact resolve eq230269 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230269
  have eq230497 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq230430
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq230430
    | exact resolve eq230430 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230430
  have eq230550 : (σ y) = (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq230497
       have r₂ := eq88266
       grind)
    | exact resolve eq230497 eq88266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88266 eq230497
  have eq230573 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq230550
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq230550
    | exact resolve eq230550 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230550
  have eq230592 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq230573
       have r₂ := eq73989
       grind)
    | exact resolve eq230573 eq73989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73989 eq230573
  have eq230599 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq230592
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq230592
    | exact resolve eq230592 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230592
  have eq241263 : (σ x) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq230599 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq230599
       grind)
    | exact resolve eq13 eq230599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230599
  have eq241380 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq241263
       have r₂ := eq109185 (σ (M.op x y))
       grind)
    | exact resolve eq241263 eq109185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109185 eq241263
  have eq241473 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq241380 eq77039
    | exact resolve eq77039 eq241380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77039 eq241380
  have eq241482 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq241473
  have eq241537 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq241482
       have r₂ := eq88892
       grind)
    | exact resolve eq241482 eq88892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88892 eq241482
  have eq241582 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq241537 eq20
    | exact resolve eq20 eq241537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241537
  have eq242003 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq241582
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq241582
    | exact resolve eq241582 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq241582
  have eq242806 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq242003 eq26
    | exact resolve eq26 eq242003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242895 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq242003 eq8361
    | exact resolve eq8361 eq242003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8361
  have eq243045 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq242003 eq75161
    | exact resolve eq75161 eq242003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75161 eq242003
  have eq243238 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq243045
  have eq243316 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq242895
       have r₂ := eq27
       grind)
    | exact resolve eq242895 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242895
  have eq244038 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq242806 eq96
    | (have j0 := eq96 X0 (σ x) (σ y)
       grind)
    | exact resolve eq96 eq242806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq242806
  have eq244197 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq244038 X0
       grind)
    | (have r₁ := eq244038 X0
       have r₂ := eq27
       grind)
    | exact resolve eq244038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244038
  have eq244222 : (τ (σ x)) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq243238 eq190
    | exact resolve eq190 eq243238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244268 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq244222
    | exact resolve eq244222 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq244222
  have eq520183 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq243316 eq243238
    | exact resolve eq243238 eq243316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243316
  have eq520218 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq520183
  have eq547493 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq520218 eq244197
    | (have r₁ := eq244197 (σ x)
       have r₂ := eq520218
       grind)
    | exact resolve eq244197 eq520218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520218
  have eq547551 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq547493
  have eq547552 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq547551
  have eq547620 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq547552 eq190
    | exact resolve eq190 eq547552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq547552
  have eq547711 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq547620
    | exact resolve eq547620 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547620
  have eq557519 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq547711 eq244268
    | exact resolve eq244268 eq547711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244268 eq547711
  have eq557570 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq557519
  have eq557698 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq557570 eq27
    | exact resolve eq27 eq557570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557699 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq557570 eq39
    | exact resolve eq39 eq557570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq557570
  have eq559331 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq557699 X0
       have i₂ := eq41 sF3 X1
       grind)
    | (have i₁ := eq557699 X0
       have i₂ := eq41 X0 sF3
       grind)
    | exact superpose eq41 eq557699
    | exact resolve eq557699 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557699
  have eq561809 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq559331
    | (have j0 := eq559331 X0 (σ y)
       grind)
    | exact resolve eq559331 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559331
  have eq563060 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq244197 x
       have i₂ := eq561809 x
       grind)
    | exact superpose eq561809 eq244197
    | (have r₁ := eq244197 x
       have r₂ := eq561809 x
       grind)
    | exact resolve eq244197 eq561809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244197 eq561809
  have eq563584 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq563060
  have eq563585 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq563584
  have eq572230 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq563585 eq243238
    | exact resolve eq243238 eq563585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243238 eq563585
  have eq572268 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq572230
  have eq572288 : x = (M.op x y) := by
    first
    | (have r₁ := eq572268
       have r₂ := eq557698
       grind)
    | exact resolve eq572268 eq557698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557698 eq572268
  have eq572310 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq572288 eq20
    | exact resolve eq20 eq572288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq572311 : ∀ X0 : G, (M.op y y) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq572288 eq38
    | exact resolve eq38 eq572288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq572904 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq572310
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq572310
    | exact resolve eq572310 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572310
  have eq574710 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq572904 eq26
    | exact resolve eq26 eq572904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq576692 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq572311 X1
       have i₂ := eq572311 X0
       grind)
    | exact superpose eq572311 eq572311
    | exact resolve eq572311 eq572311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572311
  have eq581839 : ∀ X0 : G, (M.op x y) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq576692 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq576692 X0 y
       grind)
    | exact superpose eq576692 eq18
    | (have j1 := eq576692 y X0
       grind)
    | exact resolve eq18 eq576692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq576692
  have eq582126 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq572288 eq581839
    | exact resolve eq581839 eq572288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581839
  have eq582247 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq582126 x
       have i₂ := eq41 x X0
       grind)
    | (have i₁ := eq582126 x
       have i₂ := eq41 X0 x
       grind)
    | exact superpose eq41 eq582126
    | exact resolve eq582126 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq582292 : ∀ X0 : G, (σ x) = X0 ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1683 x X0
       have i₂ := eq582126 x
       grind)
    | exact superpose eq582126 eq1683
    | (have j0 := eq1683 X0 X0
       grind)
    | exact resolve eq1683 eq582126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683 eq582126
  have eq582683 : ∀ X0 : G, (σ x) = X0 ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq582292 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq582292
    | (have j0 := eq582292 X0
       grind)
    | exact resolve eq582292 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582292
  have eq582796 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq572904 eq582683
    | (have j0 := eq582683 X0
       grind)
    | exact resolve eq582683 eq572904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582683
  have eq582844 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq582796 X0
       have j1 := eq1766 X0
       grind)
    | (have r₁ := eq582796 X0
       have r₂ := eq1766 X0
       grind)
    | (have r₁ := eq582796 (σ (M.op x y))
       have r₂ := eq1766 (σ (M.op x y))
       grind)
    | (have r₁ := eq582796 (σ (M.op x y))
       have r₂ := eq1766 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq582796 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766 eq582796
  have eq587193 : (σ (k y x)) = (σ (k x (σ (M.op x y)))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq582844 eq19066
    | exact resolve eq19066 eq582844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19066
  have eq587221 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq582844 eq375
    | exact resolve eq375 eq582844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq587554 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq587221
    | exact resolve eq587221 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq587221
  have eq587573 : (σ x) = (σ (k y x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq582844 eq587193
    | exact resolve eq587193 eq582844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587193
  have eq587819 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
    intro X0
    first
    | exact superpose eq572288 eq587554
    | exact resolve eq587554 eq572288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587554
  have eq587827 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq587573
       have i₂ := eq142
       grind)
    | exact superpose eq142 eq587573
    | exact resolve eq587573 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq587573
  have eq587966 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq587819 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq587819
    | exact resolve eq587819 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587819
  have eq587972 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq572904 eq587827
    | exact resolve eq587827 eq572904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587827
  have eq588088 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq582844 eq587972
    | exact resolve eq587972 eq582844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587972
  have eq588136 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq588088
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq588088
    | exact resolve eq588088 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq588088
  have eq588175 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq572904 eq588136
    | exact resolve eq588136 eq572904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588136
  have eq588182 : (σ (M.op x y)) = (σ y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq572288 eq588175
    | exact resolve eq588175 eq572288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588175
  have eq620582 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq588182 eq574710
    | exact resolve eq574710 eq588182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574710 eq588182
  have eq620595 : x = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq620582
       have i₂ := eq582247 sF1
       grind)
    | exact superpose eq582247 eq620582
    | exact resolve eq620582 eq582247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620582
  have eq620596 : x = (M.op (σ x) (σ y)) := by grind
  clear eq620595
  have eq621174 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq620596 eq27
    | exact resolve eq27 eq620596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq620596
  have eq623045 : ∀ X0 : G, (σ X0) ≠ x ∨ (σ (k X0 (k x (M.op x y)))) = (M.op (k (σ x) (σ (M.op x y))) (σ X0)) ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9985 X0
       have i₂ := eq582247 (k sF2 sF1)
       grind)
    | exact superpose eq582247 eq9985
    | (have j0 := eq9985 X0
       grind)
    | exact resolve eq9985 eq582247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9985 eq582247
  have eq623046 : ∀ X0 : G, (σ (k X0 (k x (M.op x y)))) = (M.op (σ x) (σ X0)) ∨ (σ X0) ≠ x ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq582844 eq623045
    | (have j0 := eq623045 X0
       grind)
    | exact resolve eq623045 eq582844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623045
  have eq623047 : ∀ X0 : G, (σ (k X0 (k x (M.op x y)))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) ≠ x ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq572904 eq623046
    | (have j0 := eq623046 X0
       grind)
    | exact resolve eq623046 eq572904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623046
  have eq623048 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ X0)) = (σ (k X0 (k x x))) ∨ (σ X0) ≠ x ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq572288 eq623047
    | (have j0 := eq623047 X0
       grind)
    | exact resolve eq623047 eq572288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572288 eq623047
  have eq623049 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) ≠ x ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq623048 X0
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq623048
    | (have j0 := eq623048 X0
       grind)
    | exact resolve eq623048 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq623048
  have eq623050 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) ≠ x ∨ (σ X0) = (M.op (k (σ x) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq623049 X0
       have i₂ := eq587966 X0
       grind)
    | exact superpose eq587966 eq623049
    | (have j0 := eq623049 X0
       grind)
    | exact resolve eq623049 eq587966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587966 eq623049
  have eq623051 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) ≠ x := by
    intro X0
    first
    | exact superpose eq582844 eq623050
    | (have j0 := eq623050 X0
       grind)
    | exact resolve eq623050 eq582844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623050
  have eq623052 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) ≠ x := by
    intro X0
    first
    | exact superpose eq572904 eq623051
    | (have j0 := eq623051 X0
       grind)
    | exact resolve eq623051 eq572904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572904 eq623051
  have eq623053 : ∀ X0 : G, (σ X0) ≠ x ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq623052 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623052
  have eq625337 : ∀ X0 : G, x ≠ X0 ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq623053 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq623053
    | (have r₁ := eq623053 (τ x)
       have r₂ := eq15 x
       grind)
    | exact resolve eq623053 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623053
  have eq667153 : x = (M.op (σ (M.op x y)) x) := by
    first
    | (have j0 := eq625337 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625337
  have eq667154 : x ≠ x ∨ (σ (M.op x y)) = (k x (σ (M.op x y))) := by
    first
    | exact superpose eq667153 eq13
    | (have j0 := eq13 x (σ (M.op x y))
       grind)
    | (have r₁ := eq13 x (σ (M.op x y))
       have r₂ := eq667153
       grind)
    | exact resolve eq13 eq667153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667153
  have eq667304 : (σ (M.op x y)) = (k x (σ (M.op x y))) := by grind
  clear eq667154
  have eq667423 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq582844 eq667304
    | exact resolve eq667304 eq582844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582844 eq667304
  have eq667507 : False := by grind
  exact eq667507

/-- `Equation3666`: `x ◇ x = (x ◇ y) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxy_x_pxy_Equation3666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X0 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq29 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq30 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30
    | (have j0 := eq30 x
       grind)
    | exact resolve eq30 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq50 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq66 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq92 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq10
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) (M.op x y))) = (k (k (σ X0) X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq30
    | exact resolve eq30 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq132 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq110
    | (have j0 := eq110 X0
       grind)
    | exact resolve eq110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq133 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq215 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X0 x) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op x x) = (M.op (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x X0 y
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) X0 (σ y)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X2 (M.op X0 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220 X0 X1 X2
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq220
    | exact resolve eq220 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq222 : ∀ X0 X1 X3 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq217 X0 X1 X3
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq217
    | exact resolve eq217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq223 : (M.op x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq215 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq215
    | (have j0 := eq215 y
       grind)
    | exact resolve eq215 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x x)) := by
    intro X0
    first
    | exact superpose eq215 eq9
    | exact resolve eq9 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq215 eq9
    | exact resolve eq9 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq226 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) (M.op x x)) := by
    intro X0
    first
    | exact superpose eq223 eq224
    | exact resolve eq224 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq227 : ∀ X1 : G, (M.op x x) = (M.op (M.op x x) (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq223 eq225
    | exact resolve eq225 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq228 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X2) ∨ (M.op X0 X0) = (k (M.op X0 X1) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op X0 X1) (M.op X0 X0)
       have r₂ := eq9 X0 X1 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
  have eq231 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | exact superpose eq66 eq231
    | exact resolve eq231 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq248 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq50
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq254 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq14 (σ X0) sF1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq14 sF2 sF1
       grind)
    | exact superpose eq14 eq42
    | (have j1 := eq14 (σ (k x (M.op x y))) (M.op (σ x) (σ (M.op x y)))
       grind)
    | exact resolve eq42 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq264 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq263
    | exact resolve eq263 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq266 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq264
    | exact resolve eq264 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq268 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq266
       have r₂ := eq232
       grind)
    | exact resolve eq266 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq266
  have eq273 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq216
    | (have j0 := eq216 (σ y)
       grind)
    | exact resolve eq216 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq216 eq9
    | exact resolve eq9 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq273 eq276
    | exact resolve eq276 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq283 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq218 eq12
    | exact resolve eq12 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq268
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq268
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq268 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq294
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq294
    | exact resolve eq294 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq304
    | exact resolve eq304 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq306 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq305
       have r₂ := eq28
       grind)
    | exact resolve eq305 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq307 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq306
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq306
    | exact resolve eq306 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq312 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq307 eq40
    | exact resolve eq40 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq321 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39 eq312
    | exact resolve eq312 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq322 : y = (M.op x y) ∨ x = y := by grind
  clear eq321
  have eq327 : y ≠ y ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq322 eq229
    | (have r₁ := eq229
       have r₂ := eq322
       grind)
    | exact resolve eq229 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq330 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq322 eq21
    | exact resolve eq21 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq331 : y = (k x y) ∨ x = y := by grind
  clear eq327
  have eq332 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq330
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq330
    | exact resolve eq330 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq355 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq268
       have i₂ := eq331
       grind)
    | exact superpose eq331 eq268
    | exact resolve eq268 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq331
  have eq361 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq355
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq355
    | exact resolve eq355 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq372 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq361 eq28
    | exact resolve eq28 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq374 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq372
       have r₂ := eq332
       grind)
    | exact resolve eq372 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq372
  have eq391 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X1) (M.op x x)) := by
    intro X0 X1
    first
    | exact superpose eq223 eq221
    | exact resolve eq221 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq273 eq222
    | exact resolve eq222 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq449 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq374 eq40
    | exact resolve eq40 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq374
  have eq461 : x = y ∨ x = y := by
    first
    | exact superpose eq39 eq449
    | exact resolve eq449 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq462 : x = y := by grind
  clear eq461
  have eq466 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq462
       grind)
    | exact superpose eq462 eq19
    | exact resolve eq19 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq467 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq462
       grind)
    | exact superpose eq462 eq25
    | exact resolve eq25 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq462
  have eq504 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq467
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq467
    | exact resolve eq467 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq507 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq223
       have i₂ := eq466
       grind)
    | exact superpose eq466 eq223
    | exact resolve eq223 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq508 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq226 X0
       have i₂ := eq466
       grind)
    | exact superpose eq466 eq226
    | exact resolve eq226 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq509 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X1
    first
    | (have i₁ := eq227 X1
       have i₂ := eq466
       grind)
    | exact superpose eq466 eq227
    | exact resolve eq227 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq512 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (k (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq466
       grind)
    | exact superpose eq466 eq283
    | (have j0 := eq283 X0
       grind)
    | (have r₁ := eq283 X0
       have r₂ := eq466
       grind)
    | exact resolve eq283 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq513 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq466
       grind)
    | exact superpose eq466 eq391
    | exact resolve eq391 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq515 : ∀ X0 : G, (M.op x x) = (k (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq512 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq517 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq504 eq27
    | exact resolve eq27 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq504
  have eq534 : ∀ X0 : G, (M.op x y) = (k (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq515 X0
       have i₂ := eq466
       grind)
    | exact superpose eq466 eq515
    | exact resolve eq515 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466 eq515
  have eq543 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq517 eq216
    | exact resolve eq216 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq544 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq517 eq219
    | exact resolve eq219 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq548 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq517 eq278
    | exact resolve eq278 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq552 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq517 eq411
    | exact resolve eq411 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq578 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq517 eq222
    | exact resolve eq222 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq579 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq517 eq221
    | exact resolve eq221 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq517
  have eq661 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq508 eq12
    | (have r₁ := eq12 (M.op (M.op x y) X0) (M.op x y)
       have r₂ := eq508 X0
       grind)
    | exact resolve eq12 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq664 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq871 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq228 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq904 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) X0) X1) (M.op (M.op (M.op x y) X0) X1)) = (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq513 eq9
    | exact resolve eq9 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq908 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq904 X0 X2 X2
       have i₂ := eq9 (M.op sF0 X0) X2 X2
       grind)
    | exact superpose eq9 eq904
    | exact resolve eq904 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq914 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq908 X2 X1 X2
       have i₂ := eq9 sF0 X2 X2
       grind)
    | exact superpose eq9 eq908
    | exact resolve eq908 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq920 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq507 eq914
    | exact resolve eq914 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq1107 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op x X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq534 eq250
    | (have j0 := eq250 (M.op x y) (M.op x X0)
       grind)
    | exact resolve eq250 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq1108 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq664 eq250
    | (have j0 := eq250 (M.op x y) (M.op (M.op x y) X0)
       grind)
    | exact resolve eq250 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq1137 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have j0 := eq1108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1138 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq1107 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1149 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq21 eq1137
    | (have j0 := eq1137 X0
       grind)
    | exact resolve eq1137 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1150 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq21 eq1138
    | (have j0 := eq1138 X0
       grind)
    | exact resolve eq1138 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1161 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq21 eq1149
    | (have j0 := eq1149 X0
       grind)
    | exact resolve eq1149 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1162 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq21 eq1150
    | (have j0 := eq1150 X0
       grind)
    | exact resolve eq1150 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1349 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) (M.op (M.op (M.op (M.op x y) X0) X1) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq920 eq9
    | exact resolve eq9 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1353 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op x y) X0) X1) (M.op (M.op (M.op x y) X0) X1)) = (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1349 X0 X1 X2 X3
       have i₂ := eq9 (M.op (M.op sF0 X0) X1) X2 X2
       grind)
    | exact superpose eq9 eq1349
    | exact resolve eq1349 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1359 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1353 X0 X2 X2 X3
       have i₂ := eq9 (M.op sF0 X0) X2 X2
       grind)
    | exact superpose eq9 eq1353
    | exact resolve eq1353 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1365 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1359 X2 X1 X2 X3
       have i₂ := eq9 sF0 X2 X2
       grind)
    | exact superpose eq9 eq1359
    | exact resolve eq1359 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq1371 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq507 eq1365
    | exact resolve eq1365 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq2052 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1371 eq9
    | exact resolve eq9 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq2061 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) (M.op (M.op (M.op (M.op x y) X0) X1) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2052 X0 X1 X2 X2 X4
       have i₂ := eq9 (M.op (M.op (M.op sF0 X0) X1) X2) X2 X2
       grind)
    | exact superpose eq9 eq2052
    | exact resolve eq2052 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2068 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op x y) X0) X1) (M.op (M.op (M.op x y) X0) X1)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2061 X0 X1 X2 X3 X4
       have i₂ := eq9 (M.op (M.op sF0 X0) X1) X2 X2
       grind)
    | exact superpose eq9 eq2061
    | exact resolve eq2061 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061
  have eq2075 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2068 X0 X2 X2 X3 X4
       have i₂ := eq9 (M.op sF0 X0) X2 X2
       grind)
    | exact superpose eq9 eq2068
    | exact resolve eq2068 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2082 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2075 X2 X1 X2 X3 X4
       have i₂ := eq9 sF0 X2 X2
       grind)
    | exact superpose eq9 eq2075
    | exact resolve eq2075 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq2087 : ∀ X0 X1 X2 X3 X4 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq507 eq2082
    | exact resolve eq2082 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082
  have eq2451 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq871 (τ X0) (τ X0)
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq871
    | (have j1 := eq132 (τ X0)
       grind)
    | exact resolve eq871 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq871
  have eq4739 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) (M.op x y)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq2087 eq9
    | exact resolve eq9 eq2087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq4750 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) (M.op x y)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq4739 X0 X1 X2 X3 X2 X5
       have i₂ := eq9 (M.op (M.op (M.op (M.op sF0 X0) X1) X2) X3) X2 X2
       grind)
    | exact superpose eq9 eq4739
    | exact resolve eq4739 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4739
  have eq4759 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) (M.op (M.op (M.op (M.op x y) X0) X1) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) (M.op x y)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq4750 X0 X1 X2 X2 X4 X5
       have i₂ := eq9 (M.op (M.op (M.op sF0 X0) X1) X2) X2 X2
       grind)
    | exact superpose eq9 eq4750
    | exact resolve eq4750 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4750
  have eq4768 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op x y) X0) X1) (M.op (M.op (M.op x y) X0) X1)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) (M.op x y)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq4759 X0 X1 X2 X3 X4 X5
       have i₂ := eq9 (M.op (M.op sF0 X0) X1) X2 X2
       grind)
    | exact superpose eq9 eq4759
    | exact resolve eq4759 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4759
  have eq4777 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) (M.op x y)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq4768 X0 X2 X2 X3 X4 X5
       have i₂ := eq9 (M.op sF0 X0) X2 X2
       grind)
    | exact superpose eq9 eq4768
    | exact resolve eq4768 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4768
  have eq4786 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) (M.op x y)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq4777 X2 X1 X2 X3 X4 X5
       have i₂ := eq9 sF0 X2 X2
       grind)
    | exact superpose eq9 eq4777
    | exact resolve eq4777 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4777
  have eq4792 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) (M.op x y)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq507 eq4786
    | exact resolve eq4786 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4786
  have eq9476 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (M.op (σ X0) (σ (M.op x y)))) ∨ (σ X0) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq255 eq10
    | (have j1 := eq255 X0
       grind)
    | exact resolve eq10 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq13159 : ∀ X0 X1 : G, (k (k X0 (σ X1)) (σ (M.op x y))) = (σ (k (M.op (τ X0) X1) (M.op x y))) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 (M.op (τ X0) X1)
       have i₂ := eq248 X0 X1
       grind)
    | exact superpose eq248 eq30
    | (have j1 := eq248 X0 X1
       grind)
    | exact resolve eq30 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq16402 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5)) = (M.op (M.op x y) (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | exact superpose eq4792 eq9
    | exact resolve eq9 eq4792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4792
  have eq16419 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4)) = (M.op (M.op x y) (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq16402 X0 X1 X2 X3 X4 X2 X6
       have i₂ := eq9 (M.op (M.op (M.op (M.op (M.op sF0 X0) X1) X2) X3) X4) X2 X2
       grind)
    | exact superpose eq9 eq16402
    | exact resolve eq16402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16402
  have eq16434 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3)) = (M.op (M.op x y) (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq16419 X0 X1 X2 X3 X2 X5 X6
       have i₂ := eq9 (M.op (M.op (M.op (M.op sF0 X0) X1) X2) X3) X2 X2
       grind)
    | exact superpose eq9 eq16419
    | exact resolve eq16419 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16419
  have eq16449 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) (M.op (M.op (M.op (M.op x y) X0) X1) X2)) = (M.op (M.op x y) (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq16434 X0 X1 X2 X2 X4 X5 X6
       have i₂ := eq9 (M.op (M.op (M.op sF0 X0) X1) X2) X2 X2
       grind)
    | exact superpose eq9 eq16434
    | exact resolve eq16434 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16434
  have eq16464 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op x y) X0) X1) (M.op (M.op (M.op x y) X0) X1)) = (M.op (M.op x y) (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq16449 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq9 (M.op (M.op sF0 X0) X1) X2 X2
       grind)
    | exact superpose eq9 eq16449
    | exact resolve eq16449 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16449
  have eq16479 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq16464 X0 X2 X2 X3 X4 X5 X6
       have i₂ := eq9 (M.op sF0 X0) X2 X2
       grind)
    | exact superpose eq9 eq16464
    | exact resolve eq16464 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16464
  have eq16494 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq16479 X2 X1 X2 X3 X4 X5 X6
       have i₂ := eq9 sF0 X2 X2
       grind)
    | exact superpose eq9 eq16479
    | exact resolve eq16479 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16479
  have eq16500 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) X3) X4) X5) X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | exact superpose eq507 eq16494
    | exact resolve eq16494 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq16494
  have eq17391 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ x) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) X0) ∨ (τ X0) = x ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1162 (τ x)
       have i₂ := eq254 x x
       grind)
    | exact superpose eq254 eq1162
    | (have j1 := eq254 x X0
       grind)
    | exact resolve eq1162 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq17392 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (τ X0) = (M.op x y) ∨ (τ X0) = (M.op (M.op x y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1161 (τ x)
       have i₂ := eq254 sF0 x
       grind)
    | exact superpose eq254 eq1161
    | (have j1 := eq254 (M.op x y) X0
       grind)
    | exact resolve eq1161 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq1161
  have eq17425 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (τ X0) = (M.op x y) ∨ (τ X0) = (M.op (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq17392
    | (have j0 := eq17392 X0
       grind)
    | exact resolve eq17392 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17392
  have eq17426 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ x) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) X0) ∨ (τ X0) = x ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17391 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17391
    | (have j0 := eq17391 X0
       grind)
    | exact resolve eq17391 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17391
  have eq17487 : ∀ X0 : G, (τ X0) = (M.op (M.op x y) (τ X0)) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (τ X0) = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq21 eq17425
    | (have j0 := eq17425 X0
       grind)
    | exact resolve eq17425 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17425
  have eq17488 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (σ (M.op x y)) = (M.op (k (σ x) X0) (σ (M.op x y))) ∨ (τ X0) = x ∨ (σ (M.op x y)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq17426 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17426
    | (have j0 := eq17426 X0
       grind)
    | exact resolve eq17426 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17426
  have eq61336 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0 (τ X0)
       have i₂ := eq2451 X0
       grind)
    | exact superpose eq2451 eq50
    | (have j1 := eq2451 X0
       grind)
    | exact resolve eq50 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451
  have eq61338 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61336 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61336
    | (have j0 := eq61336 X0
       grind)
    | exact resolve eq61336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61336
  have eq61339 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq61338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61338
  have eq203081 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k x (τ X0)) ∨ (σ (M.op x y)) = (M.op (k (σ x) X0) (σ (M.op x y))) ∨ (τ X0) = x ∨ (σ (M.op x y)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq12 x (τ X0)
       have i₂ := eq17488 X0
       grind)
    | exact superpose eq17488 eq12
    | (have j1 := eq17488 X0
       grind)
    | (have r₁ := eq12 x (τ X0)
       have r₂ := eq17488 X0
       grind)
    | (have r₁ := eq12 (k (σ x) X0) (σ (M.op x y))
       have r₂ := eq17488 X0
       grind)
    | exact resolve eq12 eq17488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17488
  have eq203086 : ∀ X0 : G, (τ X0) = (k x (τ X0)) ∨ (σ (M.op x y)) = (M.op (k (σ x) X0) (σ (M.op x y))) ∨ (τ X0) = x ∨ (σ (M.op x y)) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq203081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203081
  have eq204537 : ∀ X0 : G, (M.op x y) = (k (τ X0) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (τ X0) = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq17487 eq664
    | (have j1 := eq17487 X0
       grind)
    | exact resolve eq664 eq17487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17487
  have eq204632 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (τ X0) = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq204537 eq50
    | (have j1 := eq204537 X0
       grind)
    | exact resolve eq50 eq204537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204537
  have eq204634 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq21 eq204632
    | (have j0 := eq204632 X0
       grind)
    | exact resolve eq204632 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204632
  have eq204643 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq11 X0
       have i₂ := eq204634 X0
       grind)
    | exact superpose eq204634 eq11
    | (have j1 := eq204634 X0
       grind)
    | exact resolve eq11 eq204634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204634
  have eq204675 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq21 eq204643
    | (have j0 := eq204643 X0
       grind)
    | exact resolve eq204643 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204643
  have eq204698 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq204675 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op X0 (σ (M.op x y)))
       have j1 := eq204675 X0
       grind)
    | exact resolve eq14 eq204675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204675
  have eq204709 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq204698 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204698
  have eq207696 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (σ (M.op x y)) = (M.op (k (σ x) X0) (σ (M.op x y))) ∨ (τ X0) = x ∨ (σ (M.op x y)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq49 X0 x
       have i₂ := eq203086 X0
       grind)
    | exact superpose eq203086 eq49
    | (have j1 := eq203086 X0
       grind)
    | exact resolve eq49 eq203086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203086
  have eq207722 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (σ (M.op x y)) = (M.op (k (σ x) X0) (σ (M.op x y))) ∨ (τ X0) = x ∨ (σ (M.op x y)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq207696 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq207696
    | (have j0 := eq207696 X0
       grind)
    | exact resolve eq207696 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207696
  have eq207736 : ∀ X0 : G, (τ X0) = x ∨ (σ (M.op x y)) = (M.op (k (σ x) X0) (σ (M.op x y))) ∨ (k (σ x) X0) = X0 ∨ (σ (M.op x y)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq207722 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq207722
    | (have j0 := eq207722 X0
       grind)
    | exact resolve eq207722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207722
  have eq207764 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq38
       have i₂ := eq207736 sF1
       grind)
    | exact superpose eq207736 eq38
    | (have j1 := eq207736 (σ (M.op x y))
       grind)
    | exact resolve eq38 eq207736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207736
  have eq207773 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by grind
  clear eq207764
  have eq207775 : (σ (M.op x y)) = (M.op (σ (k x (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq42 eq207773
    | exact resolve eq207773 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207773
  have eq207780 : (σ (M.op x y)) = (M.op (σ (k x (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq207775
    | exact resolve eq207775 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq207775
  have eq207787 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq256 eq207780
    | exact resolve eq207780 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq207780
  have eq207799 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq207787
  have eq207886 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq207799 eq579
    | exact resolve eq579 eq207799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207799
  have eq208019 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq207886 eq544
    | exact resolve eq544 eq207886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207886
  have eq208073 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq208019
  have eq208094 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq208073 eq12
    | (have r₁ := eq12 (σ (M.op x y)) (M.op (σ x) (σ y))
       have r₂ := eq208073
       grind)
    | exact resolve eq12 eq208073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208073
  have eq208108 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq208094
  have eq208111 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq208108 eq204709
    | (have j0 := eq204709 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq204709 eq208108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204709 eq208108
  have eq208130 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq208111
  have eq208139 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq208130
       have r₂ := eq28
       grind)
    | exact resolve eq208130 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208130
  have eq208154 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq208139 eq548
    | exact resolve eq548 eq208139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq208154 eq208139
    | exact resolve eq208139 eq208154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208139 eq208154
  have eq208319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq208252
  have eq208324 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq208319
       have r₂ := eq28
       grind)
    | exact resolve eq208319 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208319
  have eq208329 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq208324 eq39
    | exact resolve eq39 eq208324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq208324
  have eq208581 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq208329
    | exact resolve eq208329 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208329
  have eq208582 : x = (M.op x y) := by grind
  clear eq208581
  have eq208586 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq208582 eq21
    | exact resolve eq21 eq208582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq208587 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (k x X0)) := by
    intro X0
    first
    | exact superpose eq208582 eq29
    | exact resolve eq29 eq208582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq208588 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (k X0 x)) := by
    intro X0
    first
    | exact superpose eq208582 eq30
    | exact resolve eq30 eq208582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq208590 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq208582 eq38
    | exact resolve eq38 eq208582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq208593 : ∀ X0 X1 : G, (k (k (σ X0) X1) (σ (M.op x y))) = (σ (k (k X0 (τ X1)) x)) := by
    intro X0 X1
    first
    | exact superpose eq208582 eq96
    | exact resolve eq96 eq208582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq208603 : ∀ X1 : G, x = (M.op x (M.op x X1)) := by
    intro X1
    first
    | exact superpose eq208582 eq509
    | exact resolve eq509 eq208582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq208610 : ∀ X0 : G, x = (k (M.op x X0) x) := by
    intro X0
    first
    | exact superpose eq208582 eq664
    | exact resolve eq664 eq208582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq208796 : ∀ X0 : G, (k X0 x) = (τ (M.op (σ X0) (σ (M.op x y)))) ∨ (σ X0) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq208582 eq9476
    | (have j0 := eq9476 X0
       grind)
    | exact resolve eq9476 eq208582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9476
  have eq208844 : ∀ X0 X1 : G, (k (k X0 (σ X1)) (σ (M.op x y))) = (σ (k (M.op (τ X0) X1) x)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq208582 eq13159
    | (have j0 := eq13159 X0 X1
       grind)
    | exact resolve eq13159 eq208582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13159
  have eq208887 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, x = (M.op x (M.op (M.op (M.op (M.op (M.op (M.op (M.op x X0) X1) X2) X3) X4) X5) X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | exact superpose eq208582 eq16500
    | exact resolve eq16500 eq208582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16500 eq208582
  have eq215228 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq208586
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq208586
    | exact resolve eq208586 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208586
  have eq215541 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq215228 eq23
    | exact resolve eq23 eq215228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq215551 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq215228 eq543
    | exact resolve eq543 eq215228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq215552 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq215228 eq544
    | exact resolve eq544 eq215228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq215555 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (M.op x y)) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq215228 eq578
    | exact resolve eq578 eq215228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq215556 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq215228 eq579
    | exact resolve eq579 eq215228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq215228
  have eq272434 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq208796 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq208796
    | exact resolve eq208796 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208796
  have eq332086 : ∀ X0 : G, (σ (k (M.op x X0) x)) = (k (k (σ (M.op x y)) (σ X0)) (σ (M.op x y))) ∨ x = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq208590 eq208844
    | exact resolve eq208844 eq208590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208844
  have eq332089 : ∀ X0 : G, (k (σ (k x X0)) (σ (M.op x y))) = (σ (k (M.op x X0) x)) ∨ x = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq208587 eq332086
    | (have j0 := eq332086 X0
       grind)
    | exact resolve eq332086 eq208587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332086
  have eq332093 : ∀ X0 : G, (σ x) = (k (σ (k x X0)) (σ (M.op x y))) ∨ x = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq332089 X0
       have i₂ := eq208610 X0
       grind)
    | exact superpose eq208610 eq332089
    | (have j0 := eq332089 X0
       grind)
    | exact resolve eq332089 eq208610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332089
  have eq332097 : ∀ X0 : G, (σ x) = (σ (k (k x X0) x)) ∨ x = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq208588 eq332093
    | (have j0 := eq332093 X0
       grind)
    | exact resolve eq332093 eq208588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332093
  have eq332100 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (k x X0) x)) ∨ x = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq332097 X0
       have i₂ := eq215541
       grind)
    | exact superpose eq215541 eq332097
    | (have j0 := eq332097 X0
       grind)
    | exact resolve eq332097 eq215541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332097
  have eq332122 : ∀ X0 : G, (σ (M.op x y)) = (k (k (σ x) X0) (σ x)) ∨ (τ X0) = x ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq93 x X0 x
       have i₂ := eq332100 (τ X0)
       grind)
    | exact superpose eq332100 eq93
    | (have j1 := eq332100 (τ X0)
       grind)
    | exact resolve eq93 eq332100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332100
  have eq332190 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (τ X0) = x ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq332122 X0
       have i₂ := eq215541
       grind)
    | exact superpose eq215541 eq332122
    | (have j0 := eq332122 X0
       grind)
    | exact resolve eq332122 eq215541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332122
  have eq332528 : ∀ X0 : G, x = (M.op x (τ X0)) ∨ (τ X0) = x ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq208603 (τ X0)
       have i₂ := eq332190 X0
       grind)
    | exact superpose eq332190 eq208603
    | (have j1 := eq332190 X0
       grind)
    | exact resolve eq208603 eq332190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208603
  have eq332947 : ∀ X0 : G, (τ X0) = x ∨ (τ X0) = x ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (τ X0) = x ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq332190 X0
       have i₂ := eq332528 X0
       grind)
    | exact superpose eq332528 eq332190
    | (have j0 := eq332190 X0
       have j1 := eq332528 X0
       grind)
    | exact resolve eq332190 eq332528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332190 eq332528
  have eq332993 : ∀ X0 : G, (τ X0) = x ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq332947 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332947
  have eq333006 : ∀ X0 : G, (σ x) = X0 ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq11 X0
       have i₂ := eq332993 X0
       grind)
    | exact superpose eq332993 eq11
    | (have j1 := eq332993 X0
       grind)
    | exact resolve eq11 eq332993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333007 : ∀ X0 X1 : G, (σ (k X0 x)) = (k (σ X0) X1) ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 X0
       have i₂ := eq332993 X1
       grind)
    | exact superpose eq332993 eq49
    | (have j1 := eq332993 X1
       grind)
    | exact resolve eq49 eq332993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq332993
  have eq333663 : ∀ X0 : G, (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq333006 X0
       have i₂ := eq215541
       grind)
    | exact superpose eq215541 eq333006
    | (have j0 := eq333006 X0
       grind)
    | exact resolve eq333006 eq215541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333006
  have eq333837 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq333663 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (k (σ (M.op x y)) X0) (σ (M.op x y)))
       have j1 := eq333663 (M.op (k (σ (M.op x y)) X0) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq333663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333663
  have eq333866 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq333837 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333837
  have eq347710 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = X0 ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq333866 x
       have i₂ := eq14 sF1 x
       grind)
    | exact superpose eq14 eq333866
    | (have j0 := eq333866 (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y)))
       have j1 := eq14 (σ (M.op x y)) X0
       grind)
    | exact resolve eq333866 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333866
  have eq347720 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = X0 ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq347710 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347710
  have eq357555 : ∀ X0 X1 : G, (τ (σ (k X0 x))) = (k (τ (σ X0)) (τ X1)) ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (σ X0) X1
       have i₂ := eq333007 X0 X1
       grind)
    | exact superpose eq333007 eq133
    | (have j1 := eq333007 X0 X1
       grind)
    | exact resolve eq133 eq333007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq333007
  have eq357667 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (k X0 x))) ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq357555 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq357555
    | (have j0 := eq357555 X0 X1
       grind)
    | exact resolve eq357555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357555
  have eq357704 : ∀ X0 X1 : G, (k X0 x) = (k X0 (τ X1)) ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq357667 X0 X1
       have i₂ := eq10 (k X0 x)
       grind)
    | exact superpose eq10 eq357667
    | (have j0 := eq357667 X0 X1
       grind)
    | exact resolve eq357667 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357667
  have eq360296 : ∀ X0 X1 : G, (k X1 X0) = (k X1 x) ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ X0)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq357704 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq357704
    | (have j0 := eq357704 X0 (σ X0)
       grind)
    | exact resolve eq357704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357704
  have eq360662 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (σ (k x X0)) (σ (M.op x y))) ∨ (k X1 X0) = (k X1 x) := by
    intro X0 X1
    first
    | exact superpose eq208587 eq360296
    | (have j0 := eq360296 X0 X1
       grind)
    | exact resolve eq360296 eq208587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208587 eq360296
  have eq360677 : ∀ X0 X1 : G, (σ (M.op x y)) = (σ (k (k x X0) x)) ∨ (k X1 X0) = (k X1 x) := by
    intro X0 X1
    first
    | exact superpose eq208588 eq360662
    | (have j0 := eq360662 X0 X1
       grind)
    | exact resolve eq360662 eq208588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208588 eq360662
  have eq361613 : ∀ X0 X1 : G, (τ (σ (M.op x y))) = (k (k x X0) x) ∨ (k X1 X0) = (k X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (k x X0) x)
       have i₂ := eq360677 X0 X1
       grind)
    | exact superpose eq360677 eq10
    | (have j1 := eq360677 X0 X1
       grind)
    | exact resolve eq10 eq360677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360677
  have eq362098 : ∀ X0 X1 : G, x = (k (k x X0) x) ∨ (k X1 X0) = (k X1 x) := by
    intro X0 X1
    first
    | exact superpose eq208590 eq361613
    | (have j0 := eq361613 X0 X1
       grind)
    | exact resolve eq361613 eq208590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208590 eq361613
  have eq362948 : ∀ X0 X1 : G, x = (k (M.op x X0) X1) ∨ x = (k (k x X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq208610 X0
       have i₂ := eq362098 X1 (M.op x X0)
       grind)
    | (have i₁ := eq208610 X0
       have i₂ := eq362098 x (M.op x X0)
       grind)
    | exact superpose eq362098 eq208610
    | (have j1 := eq362098 X1 X1
       grind)
    | exact resolve eq208610 eq362098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208610 eq362098
  have eq363485 : ∀ X7 : G, x = (k (k x X7) x) ∨ x = (k x X7) := by
    intro X7
    first
    | (have i₁ := eq362948 (M.op (M.op (M.op (M.op (M.op (M.op (M.op x x) x) x) x) x) x) x) X7
       have i₂ := eq208887 x x x x x x x
       grind)
    | exact superpose eq208887 eq362948
    | (have j0 := eq362948 x X7
       grind)
    | exact resolve eq362948 eq208887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208887 eq362948
  have eq364028 : ∀ X0 : G, (σ x) = (k (k (σ x) X0) (σ x)) ∨ x = (k x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq93 x X0 x
       have i₂ := eq363485 (τ X0)
       grind)
    | exact superpose eq363485 eq93
    | (have j1 := eq363485 (τ X0)
       grind)
    | exact resolve eq93 eq363485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq363485
  have eq364042 : ∀ X0 : G, x = (k x (τ X0)) ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq364028 X0
       have i₂ := eq215541
       grind)
    | exact superpose eq215541 eq364028
    | (have j0 := eq364028 X0
       grind)
    | exact resolve eq364028 eq215541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364028
  have eq364227 : ∀ X0 : G, (σ (k x x)) = (k (k (σ x) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq208593 x X0
       have i₂ := eq364042 X0
       grind)
    | exact superpose eq364042 eq208593
    | (have j1 := eq364042 X0
       grind)
    | exact resolve eq208593 eq364042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208593 eq364042
  have eq364456 : ∀ X0 : G, (σ (k x x)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq364227 X0
       have i₂ := eq215541
       grind)
    | exact superpose eq215541 eq364227
    | (have j0 := eq364227 X0
       grind)
    | exact resolve eq364227 eq215541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364227
  have eq364509 : ∀ X0 : G, (σ x) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq364456 X0
       have i₂ := eq61339 x
       grind)
    | exact superpose eq61339 eq364456
    | (have j0 := eq364456 X0
       grind)
    | exact resolve eq364456 eq61339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61339 eq364456
  have eq364539 : ∀ X0 : G, (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq364509 X0
       have i₂ := eq215541
       grind)
    | exact superpose eq215541 eq364509
    | (have j0 := eq364509 X0
       grind)
    | exact resolve eq364509 eq215541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364509
  have eq364540 : ∀ X0 : G, (σ (M.op x y)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq364539 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364539
  have eq366509 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq364540 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (k (σ (M.op x y)) X0) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq364540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366541 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq366509 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366509
  have eq380295 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq347720 eq215555
    | (have j1 := eq347720 X0
       grind)
    | exact resolve eq215555 eq347720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215555
  have eq380296 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq347720 eq215556
    | (have j1 := eq347720 X0
       grind)
    | exact resolve eq215556 eq347720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215556 eq347720
  have eq380364 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq380295 eq215551
    | (have j1 := eq380295 X0
       grind)
    | exact resolve eq215551 eq380295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215551 eq380295
  have eq380433 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq380364 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380364
  have eq380550 : ∀ X0 : G, X0 ≠ X0 ∨ (k (σ (M.op x y)) X0) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq380433 eq12
    | (have j1 := eq380433 X0
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) X0
       have r₂ := eq380433 X0
       grind)
    | (have r₁ := eq12 X0 (σ (M.op x y))
       have r₂ := eq380433 (M.op X0 (σ (M.op x y)))
       grind)
    | exact resolve eq12 eq380433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380433
  have eq380562 : ∀ X0 : G, (k (σ (M.op x y)) X0) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq380550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380550
  have eq381559 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq380562 eq366541
    | (have j1 := eq380562 (M.op X0 (σ (M.op x y)))
       grind)
    | exact resolve eq366541 eq380562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366541 eq380562
  have eq381770 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq381559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381559
  have eq383003 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq381770 eq552
    | (have j1 := eq381770 (M.op (M.op (σ x) (σ y)) X0)
       grind)
    | exact resolve eq552 eq381770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq381770
  have eq383245 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq383003 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383003
  have eq383374 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq383245 eq548
    | exact resolve eq548 eq383245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq383245
  have eq383475 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
  clear eq383374
  have eq385515 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq383475 eq272434
    | (have j0 := eq272434 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq272434 eq383475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272434 eq383475
  have eq385531 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq385515
  have eq385538 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) := by
    first
    | (have r₁ := eq385531
       have r₂ := eq28
       grind)
    | exact resolve eq385531 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385531
  have eq385660 : (σ (τ (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq385538 eq50
    | exact resolve eq50 eq385538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq385538
  have eq385705 : (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (σ (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq385660
       have i₂ := eq215541
       grind)
    | exact superpose eq215541 eq385660
    | exact resolve eq385660 eq215541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215541 eq385660
  have eq385719 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq385705
       have i₂ := eq11 sF4
       grind)
    | exact superpose eq11 eq385705
    | exact resolve eq385705 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385705
  have eq389101 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have j0 := eq380296 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380296
  have eq389103 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq389101
  have eq389111 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq389103
       have r₂ := eq28
       grind)
    | exact resolve eq389103 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389103
  have eq389180 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq389111 eq12
    | (have r₁ := eq12 (σ (M.op x y)) (M.op (σ x) (σ y))
       have r₂ := eq389111
       grind)
    | exact resolve eq12 eq389111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389111
  have eq389194 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq389180
  have eq389252 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq389194 eq364540
    | exact resolve eq364540 eq389194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364540 eq389194
  have eq389287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq385719 eq389252
    | exact resolve eq389252 eq385719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385719 eq389252
  have eq389293 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq389287
       have r₂ := eq28
       grind)
    | exact resolve eq389287 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389287
  have eq389357 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq389293 eq215552
    | exact resolve eq215552 eq389293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215552
  have eq389494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq389293 eq389357
    | exact resolve eq389357 eq389293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389293 eq389357
  have eq389510 : False := by grind
  exact eq389510

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_x_pxy_Equation3744 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq32 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq33 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq34 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq28
    | (have j0 := eq28 (M.op x y)
       grind)
    | exact resolve eq28 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq28 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28
    | (have j0 := eq28 x
       grind)
    | exact resolve eq28 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq41 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 x
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : y ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x y) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 x X0 y X1
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 (M.op x X1) X5
       have i₂ := eq9 X0 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 y X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 y X1 x
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X3 X1) X4 (M.op X0 x)
       have i₂ := eq9 X0 X1 x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X1) ∨ (M.op X0 X2) = (k (M.op X3 X1) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X3 X1) (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X3 X1) (M.op X0 X2)
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op X0 X2)
       have r₂ := eq9 X0 X1 X2 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq56 x X1 X2 X3 x
       have i₂ := eq9 X2 X1 x x
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq59 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq54 X0 x X2 X3 x
       have i₂ := eq9 X0 X3 x x
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq61 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq53 x x
       have i₂ := eq58 x sF0 x
       grind)
    | exact superpose eq58 eq53
    | exact resolve eq53 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 x
       have i₂ := eq59 X0 x sF0
       grind)
    | exact superpose eq59 eq55
    | exact resolve eq55 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq63 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 x
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (k (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq62 eq12
    | (have j0 := eq12 (M.op x y) X0
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq62 x
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | exact superpose eq77 eq63
    | exact resolve eq63 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq77
  have eq83 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq95 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq58
    | (have j0 := eq58 (σ y) X0 (σ x)
       grind)
    | exact resolve eq58 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (k (M.op X2 X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 X1) X0
       have i₂ := eq58 X1 X0 X2
       grind)
    | exact superpose eq58 eq12
    | (have j0 := eq12 (M.op X2 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X2 X1) X2
       have r₂ := eq58 X1 X2 X2
       grind)
    | exact resolve eq12 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq103 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op (M.op x y) X0) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq62 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq62 x
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x X0) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq61 eq103
    | (have j0 := eq103 X0
       grind)
    | (have r₁ := eq103 (M.op x y)
       have r₂ := eq61 y
       grind)
    | exact resolve eq103 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq128 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq131 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq14 sF3 (σ X0)
       grind)
    | exact superpose eq14 eq33
    | (have j1 := eq14 (σ y) (σ X0)
       grind)
    | exact resolve eq33 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq34
       have i₂ := eq14 sF1 sF1
       grind)
    | exact superpose eq14 eq34
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq34 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq137 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq35
       have i₂ := eq14 sF1 sF2
       grind)
    | exact superpose eq14 eq35
    | (have j1 := eq14 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq35 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq138 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq41
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq41
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq41 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq142 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq42
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq42
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq42 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq143 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq14 sF3 sF3
       grind)
    | exact superpose eq14 eq83
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq83 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq144 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq143
  have eq145 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq138
  have eq146 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq133
  have eq150 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq142
    | exact resolve eq142 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq154 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq150
    | exact resolve eq150 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq159 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (k (M.op (σ x) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq95 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq95 (σ x)
       grind)
    | exact resolve eq12 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ x) (σ y) X0
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq262 : y ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq64 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq64
    | (have j0 := eq64 y
       grind)
    | exact resolve eq64 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq62 eq64
    | (have j0 := eq64 (M.op x y)
       grind)
    | (have r₁ := eq64 (M.op x y)
       have r₂ := eq62 x
       grind)
    | exact resolve eq64 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq266 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq263
       have r₂ := eq18
       grind)
    | exact resolve eq263 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq267 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq266 eq146
    | exact resolve eq146 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq266
  have eq270 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq267
    | exact resolve eq267 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq271 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq270
  have eq287 : (M.op x y) ≠ (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66
    | (have j0 := eq66 x
       grind)
    | (have r₁ := eq66 x
       have r₂ := eq18
       grind)
    | exact resolve eq66 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : x = (k (M.op x y) x) := by grind
  clear eq287
  have eq291 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq290 eq137
    | exact resolve eq137 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq290
  have eq294 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq291
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq291
    | exact resolve eq291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq295 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq294
  have eq308 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq221 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq221
    | exact resolve eq221 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq363 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq295 eq59
    | exact resolve eq59 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq477 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq57 X0 X2 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq490 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq128
    | (have j0 := eq128 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq128 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 X1 : G, (σ (k (k X0 X1) x)) = (k (M.op (σ X0) (σ X1)) (σ x)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (k X0 X1)
       have i₂ := eq128 X0 X1
       grind)
    | exact superpose eq128 eq31
    | (have j1 := eq128 X0 X1
       grind)
    | exact resolve eq31 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq128
  have eq644 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq271 eq477
    | exact resolve eq477 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq477
  have eq702 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (τ (M.op (σ (M.op x y)) X0)) (τ (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq644 eq308
    | exact resolve eq308 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq707 : ∀ X0 : G, (M.op x y) = (k (τ (M.op (σ (M.op x y)) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq37 eq702
    | exact resolve eq702 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq702
  have eq869 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq895 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq308 (M.op X0 X1) X0
       have i₂ := eq869 X0 X1
       grind)
    | exact superpose eq869 eq308
    | exact resolve eq308 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq966 : ∀ X0 : G, y = (k (τ (M.op (σ y) X0)) y) := by
    intro X0
    first
    | exact superpose eq39 eq895
    | exact resolve eq895 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq2579 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq144
       grind)
    | exact superpose eq144 eq10
    | exact resolve eq10 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq2601 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq145
       grind)
    | exact superpose eq145 eq10
    | exact resolve eq10 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq2690 : (k x x) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq363 eq2601
    | exact resolve eq2601 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq2601
  have eq2708 : (k x x) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq2690
  have eq3110 : (σ (k x x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2708 eq11
    | exact resolve eq11 eq2708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2708
  have eq8459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq154
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq154
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq154 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq8459
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8459
    | exact resolve eq8459 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8459
  have eq8491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq8487
    | exact resolve eq8487 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8487
  have eq8492 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq8491
       have r₂ := eq27
       grind)
    | exact resolve eq8491 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8491
  have eq8493 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq8492
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8492
    | exact resolve eq8492 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8492
  have eq8495 : y = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq8493 eq966
    | exact resolve eq966 eq8493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8493
  have eq8524 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq38 eq8495
    | exact resolve eq8495 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8495
  have eq8529 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq8524
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq8524
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq8524
       have r₂ := eq12 x y
       grind)
    | exact resolve eq8524 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8524
  have eq8532 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq154
       have i₂ := eq8529
       grind)
    | exact superpose eq8529 eq154
    | exact resolve eq154 eq8529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq8540 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq8532
  have eq8546 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8540
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8540
    | exact resolve eq8540 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8540
  have eq8547 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8546
  have eq8587 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8547 eq59
    | exact resolve eq59 eq8547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8547
  have eq9630 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8587 eq159
    | (have j0 := eq159 (σ x)
       grind)
    | (have r₁ := eq159 (σ y)
       have r₂ := eq8587 (σ y)
       grind)
    | exact resolve eq159 eq8587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq8587
  have eq9637 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9630
       have r₂ := eq26
       grind)
    | exact resolve eq9630 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9630
  have eq10405 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9637 eq14
    | (have j0 := eq14 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq14 eq9637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9637
  have eq10406 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10405
  have eq10409 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170 eq10406
    | exact resolve eq10406 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq10406
  have eq10412 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10409
    | exact resolve eq10409 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10409
  have eq10413 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq10412
  have eq10416 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq95 eq10413
    | exact resolve eq10413 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq10413
  have eq15606 : (σ (k y x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq526 x y
       have i₂ := eq8529
       grind)
    | exact superpose eq8529 eq526
    | (have j0 := eq526 x y
       grind)
    | exact resolve eq526 eq8529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq8529
  have eq15807 : (σ (k y x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15606
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15606
    | exact resolve eq15606 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15606
  have eq15931 : (σ (k y x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15807
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15807
    | exact resolve eq15807 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15807
  have eq16051 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15931
       have i₂ := eq869 sF2 sF3
       grind)
    | exact superpose eq869 eq15931
    | exact resolve eq15931 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15931
  have eq16166 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16051
       have r₂ := eq79
       grind)
    | exact resolve eq16051 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16051
  have eq16258 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16166
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16166
    | exact resolve eq16166 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16166
  have eq16332 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16258
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16258
    | exact resolve eq16258 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16258
  have eq16397 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16332
    | exact resolve eq16332 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16332
  have eq16449 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16397
       have r₂ := eq79
       grind)
    | exact resolve eq16397 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq16397
  have eq16497 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16449
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16449
    | exact resolve eq16449 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16449
  have eq16531 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16497
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16497
    | exact resolve eq16497 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16497
  have eq16596 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq16531
       grind)
    | exact superpose eq16531 eq10
    | exact resolve eq10 eq16531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16531
  have eq16630 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq16596
    | exact resolve eq16596 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16596
  have eq16643 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq16630
       have r₂ := eq52
       grind)
    | exact resolve eq16630 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq16630
  have eq16678 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq131 x
       have i₂ := eq16643
       grind)
    | exact superpose eq16643 eq131
    | (have j0 := eq131 x
       grind)
    | exact resolve eq131 eq16643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq16679 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq16643
       grind)
    | exact superpose eq16643 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq16643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16643
  have eq16685 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq16679
  have eq16686 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq16678
  have eq16692 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16685
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16685
    | exact resolve eq16685 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16685
  have eq16693 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16686
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16686
    | exact resolve eq16686 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16686
  have eq16694 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16693
  have eq16701 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16694
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16694
    | exact resolve eq16694 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16694
  have eq16707 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16701
    | exact resolve eq16701 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16701
  have eq16735 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16707 eq59
    | exact resolve eq59 eq16707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16707
  have eq17024 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16735 eq2579
    | exact resolve eq2579 eq16735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579 eq16735
  have eq17076 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17024
    | exact resolve eq17024 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17024
  have eq17080 : (σ y) = (M.op (σ x) (σ y)) ∨ (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17076
    | exact resolve eq17076 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17076
  have eq17081 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17080
  have eq19432 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17081 eq11
    | exact resolve eq11 eq17081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17081
  have eq34179 : y = (k (τ (σ x)) y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16692 eq966
    | exact resolve eq966 eq16692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq16692
  have eq34225 : y = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq34179
    | exact resolve eq34179 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq34179
  have eq34228 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq34225
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq34225
       have r₂ := eq12 y x
       grind)
    | exact resolve eq34225 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34225
  have eq34238 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq34228
       grind)
    | exact superpose eq34228 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq34228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34228
  have eq34249 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq34238
  have eq34261 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34249
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34249
    | exact resolve eq34249 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34249
  have eq34262 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq34261
  have eq34335 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 y x X0
       have i₂ := eq34262
       grind)
    | exact superpose eq34262 eq59
    | exact resolve eq59 eq34262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34460 : x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34262
       have i₂ := eq34335 x
       grind)
    | exact superpose eq34335 eq34262
    | exact resolve eq34262 eq34335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34262
  have eq34488 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq111 y
       have i₂ := eq34335 y
       grind)
    | exact superpose eq34335 eq111
    | (have j0 := eq111 y
       grind)
    | (have r₁ := eq111 y
       have r₂ := eq34335 y
       grind)
    | exact resolve eq111 eq34335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq34490 : (M.op x y) ≠ (M.op x y) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66 y
       have i₂ := eq34335 y
       grind)
    | exact superpose eq34335 eq66
    | (have j0 := eq66 x
       grind)
    | (have r₁ := eq66 y
       have r₂ := eq34335 y
       grind)
    | exact resolve eq66 eq34335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq34335
  have eq34502 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq34460
  have eq34508 : y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq34490
       have r₂ := eq18
       grind)
    | exact resolve eq34490 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34490
  have eq34509 : y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq34488
       have r₂ := eq18
       grind)
    | exact resolve eq34488 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34488
  have eq34517 : y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34509
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34509
    | exact resolve eq34509 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34509
  have eq34518 : y = (k y (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq34517
  have eq34552 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq869 x x
       have i₂ := eq34502
       grind)
    | exact superpose eq34502 eq869
    | exact resolve eq869 eq34502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq34502
  have eq34575 : y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34508 eq14
    | (have j0 := eq14 (M.op x y) y
       grind)
    | exact resolve eq14 eq34508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34508
  have eq34586 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq34575
  have eq34598 : y = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61 eq34586
    | exact resolve eq34586 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq34586
  have eq34611 : y = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34598
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34598
    | exact resolve eq34598 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq34598
  have eq34612 : y = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by grind
  clear eq34611
  have eq34626 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq62 eq34612
    | exact resolve eq34612 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq34612
  have eq35127 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3110
       have i₂ := eq34552
       grind)
    | exact superpose eq34552 eq3110
    | exact resolve eq3110 eq34552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110 eq34552
  have eq35172 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35127
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35127
    | exact resolve eq35127 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35127
  have eq35173 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq35172
  have eq35308 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq490 y y
       have i₂ := eq34626
       grind)
    | exact superpose eq34626 eq490
    | (have j0 := eq490 y y
       grind)
    | exact resolve eq490 eq34626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq34626
  have eq35314 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq35308
  have eq35327 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35314
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35314
    | exact resolve eq35314 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35314
  have eq35329 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq35327
    | exact resolve eq35327 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35327
  have eq35330 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35329
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35329
    | exact resolve eq35329 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35329
  have eq35407 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35173 eq59
    | exact resolve eq59 eq35173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq35173
  have eq36030 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35407 eq26
    | (have j1 := eq35407 (σ y)
       grind)
    | exact resolve eq26 eq35407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq35407
  have eq36080 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36030 eq707
    | exact resolve eq707 eq36030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq36030
  have eq68636 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10416 eq35330
    | exact resolve eq35330 eq10416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10416 eq35330
  have eq68701 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq68636
  have eq68738 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq68701
       have r₂ := eq27
       grind)
    | exact resolve eq68701 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68701
  have eq68876 : (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq68738 eq36080
    | exact resolve eq36080 eq68738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36080 eq68738
  have eq68924 : (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq68876
  have eq68973 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39 eq68924
    | exact resolve eq68924 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq68924
  have eq69055 : (M.op x y) = (k y (M.op x y)) := by
    first
    | (have r₁ := eq68973
       have r₂ := eq262
       grind)
    | exact resolve eq68973 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq68973
  have eq69148 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69055 eq34518
    | exact resolve eq34518 eq69055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34518
  have eq69394 : y = (M.op x y) := by grind
  clear eq69148
  have eq70126 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq69394 eq20
    | exact resolve eq20 eq69394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq73740 : y = (k y y) := by
    first
    | exact superpose eq69394 eq69055
    | exact resolve eq69055 eq69394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69055 eq69394
  have eq74121 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19432
       have i₂ := eq73740
       grind)
    | exact superpose eq73740 eq19432
    | exact resolve eq19432 eq73740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19432 eq73740
  have eq75294 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq70126
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq70126
    | exact resolve eq70126 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70126
  have eq75617 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74121
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq74121
    | exact resolve eq74121 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq74121
  have eq75618 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq75617
  have eq80379 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75294 eq75618
    | exact resolve eq75618 eq75294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75294 eq75618
  have eq83619 : False := by grind
  exact eq83619

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
    intro X0 X1 X2 X3
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  clear eq35
  have eq48 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (k (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k x x) X0
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq10
    | exact resolve eq10 eq43
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
  have eq50 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X4 (M.op X5 X6)) X6) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq14 x X4 X5 X6
       have i₂ := eq14 x X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 X3) = (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op x X5) x X5
       have i₂ := eq14 (M.op x X5) X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq14 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq14 X0 x x (M.op x X5)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq57 X1 X0
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 X1 X2
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq57 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq57 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq95 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq88
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq106 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq118 : ∀ X0 : G, (σ (k (k y y) X0)) = (k (k (σ y) (σ y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k y y) X0
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq10
    | exact resolve eq10 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq16
    | exact resolve eq16 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X2 X1
       have i₂ := eq57 X1 X0
       grind)
    | (have i₁ := eq121 X2 X1
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq121
    | (have j0 := eq121 X2 X1
       grind)
    | (have r₁ := eq121 X0 (M.op X1 X1)
       have r₂ := eq57 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq121 X0 (M.op X0 X0)
       have r₂ := eq57 X0 (M.op X0 X0)
       grind)
    | exact resolve eq121 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X2) ≠ X3 ∨ (M.op X3 X4) = (k X4 X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq121 X4 X3
       have i₂ := eq14 X3 X0 X1 X2
       grind)
    | exact superpose eq14 eq121
    | (have j0 := eq121 X4 X3
       grind)
    | (have r₁ := eq121 X0 (M.op (M.op X1 (M.op X2 X3)) X3)
       have r₂ := eq14 (M.op (M.op X1 (M.op X2 X3)) X3) X1 X2 X3
       grind)
    | exact resolve eq121 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq162 : (σ (k (k y y) x)) = (k (k (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq39 (k y y)
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq39
    | exact resolve eq39 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq147 eq16
    | exact resolve eq16 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (σ (k (k (M.op x y) (M.op x y)) x)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq147 eq39
    | exact resolve eq39 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k (M.op X1 X1) X2) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X1) X2
       have i₂ := eq56 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq56 X0 X1 x
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 (M.op X1 X1) X2
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X0) x) X1
       have r₂ := eq56 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq56 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X2 (M.op X1 X1)) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X2 (M.op X1 X1)
       have i₂ := eq56 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq121 X0 X1
       have i₂ := eq56 X0 X1 x
       grind)
    | exact superpose eq56 eq121
    | (have j0 := eq121 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq121 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq56 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq121 X0 (M.op X1 X1)
       have r₂ := eq56 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq121 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq305 : ∀ X1 X2 : G, (k X2 (M.op X1 X1)) = (M.op (M.op X1 X1) X2) := by
    intro X1 X2
    first
    | (have j0 := eq300 x X1 X2
       grind)
    | (have r₁ := eq300 x X1 X2
       have r₂ := eq57 x X1
       grind)
    | (have r₁ := eq300 X1 x X2
       have r₂ := eq57 x X1
       grind)
    | exact resolve eq300 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq306 : ∀ X1 X2 : G, (k (M.op X1 X1) X2) = (M.op X2 (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq294 x X1 X2
       grind)
    | (have r₁ := eq294 x X1 X2
       have r₂ := eq57 x X1
       grind)
    | (have r₁ := eq294 X1 x X2
       have r₂ := eq57 x X1
       grind)
    | exact resolve eq294 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq343 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq34
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) x)) = (k (k X0 (σ X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq39
    | exact resolve eq39 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq396 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 (τ X1)) X2
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq478 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op (M.op X2 (M.op X3 X4)) X4) X5) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X2 X3 X4 x X5
       have i₂ := eq53 x X0
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq590 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X4 X5)) X5) = (M.op (M.op (M.op X0 (M.op x y)) y) X2) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq50 (M.op x X2) x X2 X3 X4 X5
       have i₂ := eq53 (M.op x X2) X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1069 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op x y)) y) X2) ≠ X3 ∨ (M.op X3 X4) = (k X4 X3) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq135 (M.op x X2) x X2 X3 X4
       have i₂ := eq53 (M.op x X2) X0
       grind)
    | exact superpose eq53 eq135
    | (have j0 := eq135 X0 x X2 X3 X4
       grind)
    | (have r₁ := eq135 x x y (M.op X0 X0) X4
       have r₂ := eq53 X0 x
       grind)
    | exact resolve eq135 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq1168 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X0
       have i₂ := eq57 (σ X0) X1
       grind)
    | (have i₁ := eq84 X0 X0
       have i₂ := eq57 X0 (σ X0)
       grind)
    | exact superpose eq57 eq84
    | exact resolve eq84 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1190 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1191 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1190 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1206 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq10484 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq10517 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49 eq10484
    | exact resolve eq10484 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10484
  have eq10520 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq78 x x x
       grind)
    | (have r₁ := eq10517
       have r₂ := eq78 x (k x x) x
       grind)
    | (have r₁ := eq10517
       have r₂ := eq78 x x x
       grind)
    | exact resolve eq10517 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq10517
  have eq10523 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq10520
       grind)
    | exact superpose eq10520 eq43
    | exact resolve eq43 eq10520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq10536 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10523
       have i₂ := eq57 x X0
       grind)
    | (have i₁ := eq10523
       have i₂ := eq57 X0 x
       grind)
    | exact superpose eq57 eq10523
    | exact resolve eq10523 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10523
  have eq10585 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | (have i₁ := eq10536 x
       have i₂ := eq53 x X0
       grind)
    | exact superpose eq53 eq10536
    | exact resolve eq10536 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10588 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10536 x
       have i₂ := eq56 X0 x X1
       grind)
    | (have i₁ := eq10536 (M.op X0 X0)
       have i₂ := eq56 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq56 eq10536
    | exact resolve eq10536 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11011 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1206 X1 (M.op X0 X0)
       have i₂ := eq305 X0 (M.op X0 X0)
       grind)
    | exact superpose eq305 eq1206
    | (have j0 := eq1206 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq1206 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11129 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1206 X0 (τ X1)
       grind)
    | exact superpose eq1206 eq34
    | (have j1 := eq1206 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq11175 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11129 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq11129
    | (have j0 := eq11129 X0 X1
       grind)
    | exact resolve eq11129 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11129
  have eq11184 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ x) (σ x)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11011 X0 X1
       have i₂ := eq10536 (M.op X0 X0)
       grind)
    | exact superpose eq10536 eq11011
    | (have j0 := eq11011 X0 X1
       grind)
    | exact resolve eq11011 eq10536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11011
  have eq11189 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11175 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq11175
    | (have j0 := eq11175 X0 X1
       grind)
    | exact resolve eq11175 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11175
  have eq11195 : ∀ X1 : G, (M.op X1 X1) = (k (σ x) (σ x)) ∨ (M.op X1 X1) = (k (σ x) (σ x)) := by
    intro X1
    first
    | (have i₁ := eq11184 x X1
       have i₂ := eq10536 x
       grind)
    | exact superpose eq10536 eq11184
    | (have j0 := eq11184 x X1
       grind)
    | exact resolve eq11184 eq10536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11184
  have eq11196 : ∀ X1 : G, (M.op X1 X1) = (k (σ x) (σ x)) := by
    intro X1
    first
    | (have j0 := eq11195 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11195
  have eq11205 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq11196 x
       have i₂ := eq53 x X0
       grind)
    | exact superpose eq53 eq11196
    | exact resolve eq11196 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq11208 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11196 x
       have i₂ := eq56 X0 x X1
       grind)
    | (have i₁ := eq11196 (M.op X0 X0)
       have i₂ := eq56 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq56 eq11196
    | exact resolve eq11196 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11291 : (k (σ x) (σ x)) = (σ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq10536 x
       have i₂ := eq11196 x
       grind)
    | exact superpose eq11196 eq10536
    | exact resolve eq10536 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10536
  have eq11358 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq11196 eq49
    | exact resolve eq49 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq11378 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11358 X0
       have i₂ := eq10520
       grind)
    | exact superpose eq10520 eq11358
    | exact resolve eq11358 eq10520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11358
  have eq12736 : ∀ X0 X1 X2 : G, (σ (k (k X1 (τ (M.op X0 X0))) X2)) = (k (M.op (M.op X0 X0) (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396 X1 (M.op X0 X0) X2
       have i₂ := eq305 X0 (σ X1)
       grind)
    | exact superpose eq305 eq396
    | exact resolve eq396 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq12875 : ∀ X0 X1 X2 : G, (k (k (σ x) (σ x)) (σ X2)) = (σ (k (k X1 (τ (M.op X0 X0))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12736 X0 X1 X2
       have i₂ := eq11208 X0 (σ X1)
       grind)
    | exact superpose eq11208 eq12736
    | exact resolve eq12736 eq11208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12736
  have eq12913 : ∀ X1 X2 : G, (k (k (σ x) (σ x)) (σ X2)) = (σ (k (k X1 (M.op x x)) X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq12875 x X1 X2
       have i₂ := eq11378 x
       grind)
    | exact superpose eq11378 eq12875
    | exact resolve eq12875 eq11378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12875
  have eq12928 : ∀ X1 X2 : G, (k (k (σ x) (σ x)) (σ X2)) = (σ (k (M.op (M.op x x) X1) X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq12913 X1 X2
       have i₂ := eq305 x X1
       grind)
    | exact superpose eq305 eq12913
    | exact resolve eq12913 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12913
  have eq12933 : ∀ X2 : G, (k (k (σ x) (σ x)) (σ X2)) = (σ (k (k (σ x) (σ x)) X2)) := by
    intro X2
    first
    | (have i₁ := eq12928 x X2
       have i₂ := eq11208 x x
       grind)
    | exact superpose eq11208 eq12928
    | exact resolve eq12928 eq11208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12928
  have eq12935 : ∀ X2 : G, (σ (k (k x x) X2)) = (σ (k (k (σ x) (σ x)) X2)) := by
    intro X2
    first
    | exact superpose eq48 eq12933
    | exact resolve eq12933 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq12933
  have eq12937 : ∀ X2 : G, (σ (k (M.op x x) X2)) = (σ (k (k (σ x) (σ x)) X2)) := by
    intro X2
    first
    | (have i₁ := eq12935 X2
       have i₂ := eq10520
       grind)
    | exact superpose eq10520 eq12935
    | exact resolve eq12935 eq10520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12935
  have eq12939 : ∀ X2 : G, (σ (M.op X2 (M.op x x))) = (σ (k (k (σ x) (σ x)) X2)) := by
    intro X2
    first
    | (have i₁ := eq12937 X2
       have i₂ := eq306 x X2
       grind)
    | exact superpose eq306 eq12937
    | exact resolve eq12937 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12937
  have eq15779 : ∀ X2 X3 X4 X5 : G, (k (σ x) (σ x)) = (M.op (M.op (M.op X2 (M.op X3 X4)) X4) X5) := by
    intro X2 X3 X4 X5
    first
    | exact superpose eq11205 eq478
    | exact resolve eq478 eq11205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq15946 : ∀ X4 : G, (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) X4) := by
    intro X4
    first
    | (have i₁ := eq15779 (M.op x (M.op x (M.op x x))) x x X4
       have i₂ := eq15779 x x (M.op x x) x
       grind)
    | exact superpose eq15779 eq15779
    | exact resolve eq15779 eq15779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16099 : ∀ X3 : G, (M.op X3 (k (σ x) (σ x))) = (k (k (σ x) (σ x)) X3) := by
    intro X3
    first
    | (have i₁ := eq306 (M.op (M.op x (M.op X3 x)) x) x
       have i₂ := eq15779 x X3 x (M.op (M.op x (M.op X3 x)) x)
       grind)
    | exact superpose eq15779 eq306
    | exact resolve eq306 eq15779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15779
  have eq16350 : ∀ X0 : G, (k X0 (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq15946 eq305
    | exact resolve eq305 eq15946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq16490 : ∀ X0 : G, (k (σ x) (σ x)) = (k X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq15946 eq16350
    | exact resolve eq16350 eq15946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16350
  have eq18169 : ∀ X0 : G, (σ (k (k (σ x) (σ x)) x)) = (k (k X0 (σ (k (σ x) (σ x)))) (σ x)) := by
    intro X0
    first
    | exact superpose eq16490 eq350
    | exact resolve eq350 eq16490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq18176 : ∀ X0 : G, (σ (k (k (σ x) (σ x)) x)) = (k (k X0 (k (σ x) (σ x))) (σ x)) := by
    intro X0
    first
    | exact superpose eq11291 eq18169
    | exact resolve eq18169 eq11291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18169
  have eq18194 : (k (k (σ x) (σ x)) (σ x)) = (σ (k (k (σ x) (σ x)) x)) := by
    first
    | exact superpose eq16490 eq18176
    | exact resolve eq18176 eq16490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16490 eq18176
  have eq18229 : ∀ X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X4 X5)) X5) = (M.op (k (σ x) (σ x)) X2) := by
    intro X2 X3 X4 X5
    first
    | exact superpose eq11205 eq590
    | exact resolve eq590 eq11205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq18230 : ∀ X3 X4 X5 : G, (k (σ x) (σ x)) = (M.op (M.op X3 (M.op X4 X5)) X5) := by
    intro X3 X4 X5
    first
    | exact superpose eq15946 eq18229
    | exact resolve eq18229 eq15946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18229
  have eq19241 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1191 X0
       have i₂ := eq11196 (σ X0)
       grind)
    | exact superpose eq11196 eq1191
    | (have j0 := eq1191 X0
       grind)
    | exact resolve eq1191 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq19252 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq19241 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq19241
    | (have j0 := eq19241 (τ X0)
       grind)
    | exact resolve eq19241 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq19241
  have eq19261 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq19252 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq19252
    | (have j0 := eq19252 X0
       grind)
    | exact resolve eq19252 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19252
  have eq19269 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k (σ x) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19261 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq19261
    | (have j0 := eq19261 X0
       grind)
    | exact resolve eq19261 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19261
  have eq19912 : x ≠ (M.op x x) ∨ x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq19269 x
       have i₂ := eq10520
       grind)
    | exact superpose eq10520 eq19269
    | (have j0 := eq19269 x
       grind)
    | exact resolve eq19269 eq10520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19947 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ x = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq19912
       have i₂ := eq57 x X0
       grind)
    | (have i₁ := eq19912
       have i₂ := eq57 X0 x
       grind)
    | exact superpose eq57 eq19912
    | exact resolve eq19912 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19912
  have eq20047 : ∀ X2 X3 X4 : G, (M.op (k (σ x) (σ x)) X2) ≠ X3 ∨ (M.op X3 X4) = (k X4 X3) := by
    intro X2 X3 X4
    first
    | exact superpose eq11205 eq1069
    | (have j0 := eq1069 x X2 X3 X4
       grind)
    | exact resolve eq1069 eq11205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069 eq11205
  have eq20048 : ∀ X3 X4 : G, (k (σ x) (σ x)) ≠ X3 ∨ (M.op X3 X4) = (k X4 X3) := by
    intro X3 X4
    first
    | exact superpose eq15946 eq20047
    | (have j0 := eq20047 x X3 X4
       grind)
    | (have r₁ := eq20047 X4 (k (σ x) (σ x)) X4
       have r₂ := eq15946 X4
       grind)
    | exact resolve eq20047 eq15946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20047
  have eq23421 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq11196 (σ X0)
       grind)
    | exact superpose eq11196 eq106
    | (have j0 := eq106 X0
       grind)
    | exact resolve eq106 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq23505 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq23421 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23421
    | (have j0 := eq23421 y
       grind)
    | exact resolve eq23421 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23421
  have eq23528 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq23505
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq23505
    | exact resolve eq23505 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq23505
  have eq23546 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have j1 := eq133 x (σ y) (σ y)
       grind)
    | (have r₁ := eq23528
       have r₂ := eq133 (σ y) (k (σ y) (σ y)) x
       grind)
    | (have r₁ := eq23528
       have r₂ := eq133 (σ y) (σ y) x
       grind)
    | exact resolve eq23528 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23528
  have eq23552 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq20048 (σ y) (σ y)
       grind)
    | (have r₁ := eq23546
       have r₂ := eq20048 (σ y) x
       grind)
    | exact resolve eq23546 eq20048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23546
  have eq23559 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq23552 eq119
    | exact resolve eq119 eq23552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq23589 : (M.op x x) = (k y y) := by
    first
    | (have i₁ := eq23559
       have i₂ := eq11378 sF3
       grind)
    | exact superpose eq11378 eq23559
    | exact resolve eq23559 eq11378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23559
  have eq23604 : (k (k (σ y) (σ y)) (σ x)) = (σ (k (M.op x x) x)) := by
    first
    | (have i₁ := eq162
       have i₂ := eq23589
       grind)
    | exact superpose eq23589 eq162
    | exact resolve eq162 eq23589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq23611 : y ≠ (M.op x x) ∨ y = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq19269 y
       have i₂ := eq23589
       grind)
    | exact superpose eq23589 eq19269
    | (have j0 := eq19269 y
       grind)
    | exact resolve eq19269 eq23589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19269
  have eq23628 : (k (k (σ y) (σ y)) (σ x)) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq23604
       have i₂ := eq306 x x
       grind)
    | exact superpose eq306 eq23604
    | exact resolve eq23604 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23604
  have eq23635 : (σ (M.op x (M.op x x))) = (k (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq23552 eq23628
    | exact resolve eq23628 eq23552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23628
  have eq23642 : (σ (M.op x (M.op x x))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq23635
       have i₂ := eq306 sF3 sF2
       grind)
    | exact superpose eq306 eq23635
    | exact resolve eq23635 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23635
  have eq23658 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq148 X0
       have i₂ := eq11196 (σ X0)
       grind)
    | exact superpose eq11196 eq148
    | (have j0 := eq148 X0
       grind)
    | exact resolve eq148 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq23659 : ∀ X0 : G, (M.op X0 X0) ≠ y ∨ y = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq23611
       have i₂ := eq57 x X0
       grind)
    | (have i₁ := eq23611
       have i₂ := eq57 X0 x
       grind)
    | exact superpose eq57 eq23611
    | exact resolve eq23611 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23611
  have eq23866 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq23658
    | (have j0 := eq23658 (M.op x y)
       grind)
    | exact resolve eq23658 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23658
  have eq23887 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq147 eq23866
    | exact resolve eq23866 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq23866
  have eq23912 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have j1 := eq133 x (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq23887
       have r₂ := eq133 (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y))) x
       grind)
    | (have r₁ := eq23887
       have r₂ := eq133 (σ (M.op x y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq23887 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq23887
  have eq23926 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq20048 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq23912
       have r₂ := eq20048 (σ (M.op x y)) x
       grind)
    | exact resolve eq23912 eq20048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20048 eq23912
  have eq23973 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq23926 eq181
    | exact resolve eq181 eq23926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq24003 : (M.op x x) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq23973
       have i₂ := eq11378 sF1
       grind)
    | exact superpose eq11378 eq23973
    | exact resolve eq23973 eq11378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23973
  have eq24018 : (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) = (σ (k (M.op x x) x)) := by
    first
    | exact superpose eq24003 eq185
    | exact resolve eq185 eq24003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq24003
  have eq24042 : (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq24018
       have i₂ := eq306 x x
       grind)
    | exact superpose eq306 eq24018
    | exact resolve eq24018 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24018
  have eq24049 : (σ (M.op x (M.op x x))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq23926 eq24042
    | exact resolve eq24042 eq23926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23926 eq24042
  have eq24056 : (σ (M.op x (M.op x x))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq24049
       have i₂ := eq306 sF1 sF2
       grind)
    | exact superpose eq306 eq24049
    | exact resolve eq24049 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24049
  have eq25263 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k (σ x) (σ x)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq343 X0 X1
       have i₂ := eq11196 (τ X0)
       grind)
    | exact superpose eq11196 eq343
    | (have j0 := eq343 X0 X1
       grind)
    | exact resolve eq343 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq25343 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X0) X1)) = (k X2 (σ (τ X2))) ∨ (k (σ x) (σ x)) = (τ X2) ∨ (M.op (M.op X0 X0) X1) = (τ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25263 X0 (τ X0)
       have i₂ := eq56 X0 (τ X0) x
       grind)
    | exact superpose eq56 eq25263
    | (have j0 := eq25263 X2 X1
       grind)
    | exact resolve eq25263 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq25263
  have eq25433 : ∀ X0 X1 X2 : G, (k X2 X2) = (σ (M.op (M.op X0 X0) X1)) ∨ (k (σ x) (σ x)) = (τ X2) ∨ (M.op (M.op X0 X0) X1) = (τ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25343 X0 X1 X2
       have i₂ := eq15 X2
       grind)
    | exact superpose eq15 eq25343
    | (have j0 := eq25343 X0 X1 X2
       grind)
    | exact resolve eq25343 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25343
  have eq25496 : ∀ X0 X1 X2 : G, (k (σ x) (σ x)) = (k X2 X2) ∨ (k (σ x) (σ x)) = (τ X2) ∨ (M.op (M.op X0 X0) X1) = (τ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25433 X0 X1 X2
       have i₂ := eq10588 X0 X1
       grind)
    | exact superpose eq10588 eq25433
    | (have j0 := eq25433 X0 X1 X2
       grind)
    | exact resolve eq25433 eq10588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10588 eq25433
  have eq25541 : ∀ X2 : G, (k (σ x) (σ x)) = (τ X2) ∨ (k (σ x) (σ x)) = (k X2 X2) ∨ (k (σ x) (σ x)) = (τ X2) := by
    intro X2
    first
    | (have i₁ := eq25496 x x X2
       have i₂ := eq11208 x x
       grind)
    | exact superpose eq11208 eq25496
    | (have j0 := eq25496 x x X2
       grind)
    | exact resolve eq25496 eq11208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11208 eq25496
  have eq25542 : ∀ X2 : G, (k (σ x) (σ x)) = (k X2 X2) ∨ (k (σ x) (σ x)) = (τ X2) := by
    intro X2
    first
    | (have j0 := eq25541 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25541
  have eq26776 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11189 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11189
  have eq27286 : ∀ X0 : G, y ≠ (M.op x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq26776 X0 y
       have i₂ := eq23589
       grind)
    | exact superpose eq23589 eq26776
    | (have j0 := eq26776 X0 y
       grind)
    | exact resolve eq26776 eq23589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26776
  have eq38849 : ∀ X0 : G, (σ (k (k y y) X0)) = (k (M.op (σ y) (σ y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq23552 eq118
    | exact resolve eq118 eq23552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq23552
  have eq38850 : ∀ X0 : G, (σ (k (k y y) X0)) = (M.op (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq38849 X0
       have i₂ := eq306 sF3 (σ X0)
       grind)
    | exact superpose eq306 eq38849
    | exact resolve eq38849 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38849
  have eq38851 : ∀ X0 : G, (σ (k (M.op x x) X0)) = (M.op (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq38850 X0
       have i₂ := eq23589
       grind)
    | exact superpose eq23589 eq38850
    | exact resolve eq38850 eq23589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23589 eq38850
  have eq38852 : ∀ X0 : G, (σ (M.op X0 (M.op x x))) = (M.op (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq38851 X0
       have i₂ := eq306 x X0
       grind)
    | exact superpose eq306 eq38851
    | exact resolve eq38851 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38851
  have eq45157 : (k (k (σ x) (σ x)) (σ x)) = (σ (M.op x (k (σ x) (σ x)))) := by
    first
    | exact superpose eq16099 eq18194
    | exact resolve eq18194 eq16099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18194
  have eq45158 : (M.op (σ x) (k (σ x) (σ x))) = (σ (M.op x (k (σ x) (σ x)))) := by
    first
    | exact superpose eq16099 eq45157
    | exact resolve eq45157 eq16099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45157
  have eq47182 : (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq24056
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq24056
    | exact resolve eq24056 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23642 eq24056
  have eq47183 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47182
       have i₂ := eq57 sF3 x
       grind)
    | (have i₁ := eq47182
       have i₂ := eq57 X0 sF3
       grind)
    | exact superpose eq57 eq47182
    | exact resolve eq47182 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47182
  have eq47258 : (M.op (σ x) (k (σ x) (σ x))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq47183 x
       have i₂ := eq11196 x
       grind)
    | exact superpose eq11196 eq47183
    | exact resolve eq47183 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47183
  have eq48146 : (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op x (k (σ x) (σ x)))) := by
    first
    | exact superpose eq47258 eq45158
    | exact resolve eq45158 eq47258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45158 eq47258
  have eq49743 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq11196 eq48146
    | exact resolve eq48146 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48146
  have eq51704 : ∀ X2 : G, (σ (M.op X2 (M.op x x))) = (σ (M.op X2 (k (σ x) (σ x)))) := by
    intro X2
    first
    | exact superpose eq16099 eq12939
    | exact resolve eq12939 eq16099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12939 eq16099
  have eq52848 : ∀ X0 : G, (τ X0) ≠ (k X0 X0) ∨ (τ X0) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq25542 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25542
  have eq53018 : ∀ X0 : G, (τ (σ X0)) ≠ (σ (k X0 X0)) ∨ (τ (σ X0)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq52848 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq52848
    | (have j0 := eq52848 (σ X0)
       grind)
    | exact resolve eq52848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52848
  have eq53032 : ∀ X0 : G, (σ (k X0 X0)) ≠ X0 ∨ (τ (σ X0)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq53018 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq53018
    | (have j0 := eq53018 X0
       grind)
    | exact resolve eq53018 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53018
  have eq53033 : ∀ X0 : G, (σ (k X0 X0)) ≠ X0 ∨ (k (σ x) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq53032 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq53032
    | (have j0 := eq53032 X0
       grind)
    | exact resolve eq53032 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53032
  have eq53210 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ (M.op X0 (M.op x x))) (σ y)) := by
    intro X0
    first
    | exact superpose eq38852 eq18230
    | exact resolve eq18230 eq38852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18230 eq38852
  have eq56395 : ∀ X0 : G, (M.op X0 (k (σ x) (σ x))) = (τ (σ (M.op X0 (M.op x x)))) := by
    intro X0
    first
    | exact superpose eq51704 eq16
    | exact resolve eq16 eq51704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51704
  have eq56491 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq56395 X0
       have i₂ := eq16 (M.op X0 (M.op x x))
       grind)
    | exact superpose eq16 eq56395
    | exact resolve eq56395 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56395
  have eq56633 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op x x)) := by
    intro X0 X1
    first
    | exact superpose eq11196 eq56491
    | exact resolve eq56491 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11196 eq56491
  have eq79713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq79720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq79713
    | exact resolve eq79713 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79713
  have eq79731 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq79720
       have r₂ := eq27
       grind)
    | exact resolve eq79720 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79720
  have eq79778 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq79731 eq11378
    | exact resolve eq11378 eq79731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79731
  have eq79873 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq79778
    | exact resolve eq79778 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq79778
  have eq79890 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq27286 y
       grind)
    | (have r₁ := eq79873
       have r₂ := eq27286 x
       grind)
    | exact resolve eq79873 eq27286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27286 eq79873
  have eq79929 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq79890 eq11378
    | exact resolve eq11378 eq79890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79890
  have eq80017 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq79929
    | exact resolve eq79929 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq79929
  have eq80018 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq80017
  have eq80031 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq80018
       have i₂ := eq57 y X0
       grind)
    | (have i₁ := eq80018
       have i₂ := eq57 X0 y
       grind)
    | exact superpose eq57 eq80018
    | exact resolve eq80018 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80076 : y ≠ y ∨ y = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23659 y
       have i₂ := eq80018
       grind)
    | exact superpose eq80018 eq23659
    | (have r₁ := eq23659 y
       have r₂ := eq80018
       grind)
    | exact resolve eq23659 eq80018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23659 eq80018
  have eq80134 : y = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq80076
  have eq80872 : ∀ X0 : G, x ≠ x ∨ x = (k (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq19947 x
       have i₂ := eq80031 X0
       grind)
    | exact superpose eq80031 eq19947
    | (have j1 := eq80031 X0
       grind)
    | (have r₁ := eq19947 x
       have r₂ := eq80031 X0
       grind)
    | exact resolve eq19947 eq80031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19947 eq80031
  have eq80935 : ∀ X0 : G, x = (k (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq80872 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80872
  have eq86038 : y = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq80134 eq11291
    | exact resolve eq11291 eq80134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11291 eq80134
  have eq86135 : x = (M.op x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq86038
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86038
    | exact resolve eq86038 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq86038
  have eq86160 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq86135
       have i₂ := eq57 x X0
       grind)
    | (have i₁ := eq86135
       have i₂ := eq57 X0 x
       grind)
    | exact superpose eq57 eq86135
    | exact resolve eq86135 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq86135
  have eq86627 : (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq53210 (M.op x x)
       have i₂ := eq86160 (M.op x x)
       grind)
    | exact superpose eq86160 eq53210
    | exact resolve eq53210 eq86160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53210
  have eq86658 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq10585 sF0
       have i₂ := eq86160 sF0
       grind)
    | exact superpose eq86160 eq10585
    | exact resolve eq10585 eq86160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86160
  have eq86812 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq86658
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86658
    | exact resolve eq86658 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86658
  have eq86829 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq86627
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86627
    | exact resolve eq86627 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86627
  have eq86958 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq86812
    | exact resolve eq86812 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86812
  have eq86965 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq86829
    | exact resolve eq86829 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86829
  have eq90530 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq86965 eq86958
    | exact resolve eq86958 eq86965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86958 eq86965
  have eq90567 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq90530
  have eq90578 : y = (σ y) := by
    first
    | (have r₁ := eq90567
       have r₂ := eq27
       grind)
    | exact resolve eq90567 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90567
  have eq90610 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq90578 eq26
    | exact resolve eq26 eq90578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq93885 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | exact superpose eq80935 eq15946
    | (have j1 := eq80935 X1
       grind)
    | exact resolve eq15946 eq80935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15946
  have eq93945 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = (σ x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq80935 eq53033
    | (have j1 := eq80935 X0
       grind)
    | exact resolve eq53033 eq80935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53033 eq80935
  have eq93969 : ∀ X0 : G, (M.op X0 X0) = y ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq93945 X0
       grind)
    | (have r₁ := eq93945 X0
       have r₂ := eq22
       grind)
    | exact resolve eq93945 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq93945
  have eq94159 : ∀ X1 : G, (M.op X1 y) = (k y X1) ∨ x = (σ x) := by
    intro X1
    first
    | (have i₁ := eq306 x x
       have i₂ := eq93969 x
       grind)
    | exact superpose eq93969 eq306
    | exact resolve eq306 eq93969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq93969
  have eq99264 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq10585 x
       have i₂ := eq93885 sF0 x
       grind)
    | exact superpose eq93885 eq10585
    | (have j1 := eq93885 X0 X0
       grind)
    | exact resolve eq10585 eq93885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10585 eq93885
  have eq99302 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq99264 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99264
    | (have j0 := eq99264 X0
       grind)
    | exact resolve eq99264 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99264
  have eq99389 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq20 eq99302
    | (have j0 := eq99302 X0
       grind)
    | exact resolve eq99302 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99302
  have eq107057 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq94159 x
       grind)
    | exact superpose eq94159 eq103
    | exact resolve eq103 eq94159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq107129 : (σ (M.op x y)) = (k y (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq90578 eq107057
    | exact resolve eq107057 eq90578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90578 eq107057
  have eq107194 : (σ (M.op x y)) = (k y (σ x)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq107129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107129
    | exact resolve eq107129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107129
  have eq107230 : (σ (M.op x y)) = (k y (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq107194
    | exact resolve eq107194 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107194
  have eq107260 : (σ (M.op x y)) = (M.op (σ x) y) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq107230 eq94159
    | exact resolve eq94159 eq107230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94159 eq107230
  have eq107268 : (σ (M.op x y)) = (M.op (σ x) y) ∨ x = (σ x) := by grind
  clear eq107260
  have eq107276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq90610 eq107268
    | exact resolve eq107268 eq90610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107268
  have eq107285 : x = (σ x) := by
    first
    | (have r₁ := eq107276
       have r₂ := eq27
       grind)
    | exact resolve eq107276 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107276
  have eq107407 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq107285 eq90610
    | exact resolve eq90610 eq107285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107425 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq107407
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107407
    | exact resolve eq107407 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107407
  have eq107570 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq107425 eq27
    | exact resolve eq27 eq107425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq111353 : ∀ X0 : G, (σ (M.op x y)) = (k x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq107285 eq99389
    | (have j0 := eq99389 X0
       grind)
    | exact resolve eq99389 eq107285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99389 eq107285
  have eq111354 : ∀ X0 : G, (σ (M.op x y)) = (M.op x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq111353 X0
       have i₂ := eq10520
       grind)
    | exact superpose eq10520 eq111353
    | (have j0 := eq111353 X0
       grind)
    | exact resolve eq111353 eq10520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10520 eq111353
  have eq111822 : ∀ X0 : G, (σ (M.op x y)) = (τ (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq11378 x
       have i₂ := eq111354 X0
       grind)
    | (have i₁ := eq11378 X0
       have i₂ := eq111354 X0
       grind)
    | exact superpose eq111354 eq11378
    | (have j1 := eq111354 X0
       grind)
    | exact resolve eq11378 eq111354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11378 eq111354
  have eq111936 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq30 eq111822
    | (have j0 := eq111822 X0
       grind)
    | exact resolve eq111822 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq111822
  have eq111992 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq111936 X0
       grind)
    | (have r₁ := eq111936 X0
       have r₂ := eq107570
       grind)
    | exact resolve eq111936 eq107570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111936
  have eq112275 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq49743 x
       have i₂ := eq111992 x
       grind)
    | exact superpose eq111992 eq49743
    | exact resolve eq49743 eq111992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49743
  have eq112698 : (σ (M.op x y)) = (M.op (σ x) (M.op x x)) := by
    first
    | (have i₁ := eq112275
       have i₂ := eq56633 sF1 sF2
       grind)
    | exact superpose eq56633 eq112275
    | exact resolve eq112275 eq56633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56633 eq112275
  have eq112961 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq112698
       have i₂ := eq111992 x
       grind)
    | exact superpose eq111992 eq112698
    | exact resolve eq112698 eq111992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111992 eq112698
  have eq113183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90610 eq112961
    | exact resolve eq112961 eq90610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90610 eq112961
  have eq113340 : (σ (M.op x y)) = (M.op x y) := by
    first
    | exact superpose eq107425 eq113183
    | exact resolve eq113183 eq107425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107425 eq113183
  have eq113408 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq113340
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113340
    | exact resolve eq113340 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq113340
  have eq113438 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq113408
    | exact resolve eq113408 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq113408
  have eq113452 : False := by grind
  exact eq113452
