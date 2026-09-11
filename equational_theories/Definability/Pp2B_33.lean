import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq376 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ (M.op X0 X0))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq56 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq586 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq541 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq541
    | exact resolve eq541 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq734 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq74
  have eq739 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq734 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq734
    | exact resolve eq734 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq793 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq739 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq739
    | (have j0 := eq739 X0 X1
       grind)
    | exact resolve eq739 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq739
  have eq11147 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op (τ X0) (τ X0))) (σ (M.op X2 X2))) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376 X2 (σ X1) X0
       have i₂ := eq793 X0 X1
       grind)
    | exact superpose eq793 eq376
    | (have j1 := eq793 X0 X1
       grind)
    | exact resolve eq376 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq793
  have eq11209 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11147 X0 X1 X2
       have i₂ := eq586 (τ X0) (σ (M.op X2 X2))
       grind)
    | exact superpose eq586 eq11147
    | (have j0 := eq11147 X0 X1 X2
       grind)
    | exact resolve eq11147 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11147
  have eq11265 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11209 X0 X1 x
       have i₂ := eq586 x (σ X1)
       grind)
    | exact superpose eq586 eq11209
    | (have j0 := eq11209 X0 X1 x
       grind)
    | exact resolve eq11209 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq11209
  have eq11266 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11265
  have eq28309 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11266 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11266
    | exact resolve eq11266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11266
  have eq28695 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq28309 y x
       grind)
    | exact superpose eq28309 eq49
    | (have j1 := eq28309 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq28309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq28893 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq28695
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28695
    | exact resolve eq28695 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28695
  have eq28960 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq28893
    | exact resolve eq28893 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28893
  have eq28995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28960 eq28309
    | (have j0 := eq28309 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28309 eq28960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28309 eq28960
  have eq29001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq28995
    | exact resolve eq28995 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28995
  have eq29014 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq29001
       have r₂ := eq28
       grind)
    | exact resolve eq29001 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29001
  have eq29020 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq29014 eq30
    | exact resolve eq30 eq29014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29014
  have eq29160 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq29020
    | exact resolve eq29020 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29020
  have eq29161 : x = y := by grind
  clear eq29160
  have eq29181 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq29161
       grind)
    | exact superpose eq29161 eq19
    | exact resolve eq19 eq29161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29182 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq29161
       grind)
    | exact superpose eq29161 eq25
    | exact resolve eq25 eq29161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29161
  have eq29320 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29182
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29182
    | exact resolve eq29182 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29182
  have eq29343 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29320 eq27
    | exact resolve eq27 eq29320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29320
  have eq29801 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29343 eq68
    | exact resolve eq68 eq29343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq29343
  have eq29985 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq29801
       have i₂ := eq29181
       grind)
    | exact superpose eq29181 eq29801
    | exact resolve eq29801 eq29181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29181 eq29801
  have eq30014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29985 eq15
    | exact resolve eq15 eq29985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29985
  have eq30088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq30014
    | exact resolve eq30014 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq30014
  have eq30109 : False := by grind
  exact eq30109

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_y_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq528 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ X2 = X3 ∨ (k X2 X3) = (M.op X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq56 X0 X1 X3
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X2 X3 : G, (k X2 X3) = (M.op X2 X3) ∨ X2 = X3 := by
    intro X2 X3
    first
    | (have j0 := eq528 x x X2 X3
       grind)
    | (have r₁ := eq528 x x X2 X3
       have r₂ := eq56 x x X2
       grind)
    | exact resolve eq528 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq528
  have eq1373 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq536 x y
       grind)
    | exact superpose eq536 eq49
    | (have j1 := eq536 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1395 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1373
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1373
    | exact resolve eq1373 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1396 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq1395
    | exact resolve eq1395 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq1402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1396 eq536
    | (have j0 := eq536 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq536 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq1396
  have eq1409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1402
    | exact resolve eq1402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1418 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1409
       have r₂ := eq28
       grind)
    | exact resolve eq1409 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1424 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1418 eq30
    | exact resolve eq30 eq1418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1418
  have eq1442 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1424
    | exact resolve eq1424 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1424
  have eq1443 : x = y := by grind
  clear eq1442
  have eq1446 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1443
       grind)
    | exact superpose eq1443 eq19
    | exact resolve eq19 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1447 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1443
       grind)
    | exact superpose eq1443 eq25
    | exact resolve eq25 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1443
  have eq1463 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1447
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1447
    | exact resolve eq1447 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1447
  have eq1466 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1463 eq27
    | exact resolve eq27 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1463
  have eq1535 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1466 eq68
    | exact resolve eq68 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1466
  have eq1565 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1535
       have i₂ := eq1446
       grind)
    | exact superpose eq1446 eq1535
    | exact resolve eq1535 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446 eq1535
  have eq1566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1565 eq15
    | exact resolve eq15 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1566
    | exact resolve eq1566 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1566
  have eq1590 : False := by grind
  exact eq1590

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pxy_pyx_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq376 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ (M.op X0 X0))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq56 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq587 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq542 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq542
    | exact resolve eq542 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq735 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq69
  have eq740 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq735
    | exact resolve eq735 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq794 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq740 X0 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq740
    | (have j0 := eq740 X0 X1
       grind)
    | exact resolve eq740 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq740
  have eq11164 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op (τ X0) (τ X0))) (σ (M.op X2 X2))) (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376 X2 (σ X1) X0
       have i₂ := eq794 X0 X1
       grind)
    | exact superpose eq794 eq376
    | (have j1 := eq794 X0 X1
       grind)
    | exact resolve eq376 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq794
  have eq11226 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11164 X0 X1 X2
       have i₂ := eq587 (τ X0) (σ (M.op X2 X2))
       grind)
    | exact superpose eq587 eq11164
    | (have j0 := eq11164 X0 X1 X2
       grind)
    | exact resolve eq11164 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11164
  have eq11282 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11226 X0 X1 x
       have i₂ := eq587 x (σ X1)
       grind)
    | exact superpose eq587 eq11226
    | (have j0 := eq11226 X0 X1 x
       grind)
    | exact resolve eq11226 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq11226
  have eq11283 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11282
  have eq28281 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11283 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11283
    | exact resolve eq11283 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11283
  have eq28699 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq28281 y x
       grind)
    | exact superpose eq28281 eq88
    | (have j1 := eq28281 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq88 eq28281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq28881 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq28699
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28699
    | exact resolve eq28699 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28699
  have eq28945 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq28881
    | exact resolve eq28881 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28881
  have eq28967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28945 eq28281
    | (have j0 := eq28281 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28281 eq28945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28281 eq28945
  have eq28973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq28967
    | exact resolve eq28967 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28967
  have eq28986 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq28973
       have r₂ := eq28
       grind)
    | exact resolve eq28973 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28973
  have eq28992 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq28986 eq30
    | exact resolve eq30 eq28986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28986
  have eq29132 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq28992
    | exact resolve eq28992 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28992
  have eq29133 : x = y := by grind
  clear eq29132
  have eq29153 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq29133
       grind)
    | exact superpose eq29133 eq19
    | exact resolve eq19 eq29133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29154 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq29133
       grind)
    | exact superpose eq29133 eq25
    | exact resolve eq25 eq29133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29133
  have eq29292 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29154
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29154
    | exact resolve eq29154 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29154
  have eq29315 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29292 eq27
    | exact resolve eq27 eq29292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29292
  have eq29774 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29315 eq68
    | exact resolve eq68 eq29315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq29315
  have eq29958 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq29774
       have i₂ := eq29153
       grind)
    | exact superpose eq29153 eq29774
    | exact resolve eq29774 eq29153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29153 eq29774
  have eq29988 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29958 eq15
    | exact resolve eq15 eq29958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29958
  have eq30062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq29988
    | exact resolve eq29988 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq29988
  have eq30083 : False := by grind
  exact eq30083

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq98 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X1 X1) X0
       have i₂ := eq9 X1 X1 X1
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op (M.op X2 X1) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X1 X2 X3 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq24 X0 X0 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq24 X1 X0 X2 X4
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X1 (M.op X1 X1) X2
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq159 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134 x y
       grind)
    | exact superpose eq134 eq16
    | (have j1 := eq134 x y
       grind)
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq216 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1
       have i₂ := eq98 (τ X1) X0
       grind)
    | (have i₁ := eq32 X1
       have i₂ := eq98 X0 (τ X1)
       grind)
    | exact superpose eq98 eq32
    | exact resolve eq32 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq98
  have eq260 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq216 X0 (M.op X1 X1)
       grind)
    | exact superpose eq216 eq9
    | exact resolve eq9 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq159
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq159
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq159
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq159
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq159 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq1101 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1100
  have eq1640 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110 X0 (σ (M.op X0 X0)) X1 X2
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1734 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1640 X0 X1 X2
       have i₂ := eq260 (M.op X0 X0) (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2))
       grind)
    | exact superpose eq260 eq1640
    | exact resolve eq1640 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640
  have eq2338 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (σ (M.op X4 X4))) (M.op (M.op X5 X3) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq110 X4 X3 X5 (M.op X0 X0)
       have i₂ := eq116 X0 X0 X1 X0 X2
       grind)
    | (have i₁ := eq110 X0 X1 X2 (M.op X0 (M.op X4 X4))
       have i₂ := eq116 X0 X0 X4 X3 X4
       grind)
    | exact superpose eq116 eq110
    | exact resolve eq110 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq2380 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq112 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq116 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq112 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq116 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq116 eq112
    | exact resolve eq112 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq116
  have eq2473 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2380 X0 X1 x X3 x
       have i₂ := eq125 x (M.op X0 X1) x
       grind)
    | exact superpose eq125 eq2380
    | exact resolve eq2380 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq2869 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq117 X0 X1 x x X4 X5
       have i₂ := eq125 x (M.op X0 X1) x
       grind)
    | exact superpose eq125 eq117
    | exact resolve eq117 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq125
  have eq5081 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (σ (M.op X4 X4))) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1734 X4 X3 (M.op X1 X1)
       have i₂ := eq2869 X0 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq2869 eq1734
    | exact resolve eq1734 eq2869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734 eq2869
  have eq16233 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1101
       grind)
    | exact superpose eq1101 eq16
    | exact resolve eq16 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq16234 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16233
       have r₂ := eq216 x (σ x)
       grind)
    | exact resolve eq16233 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16233
  have eq199434 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X2 X2) (σ (M.op X3 X3))) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))) = X1 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2338 X4 X5 X6 (M.op X2 X2) X3 X1
       have i₂ := eq2473 X1 X0 X2
       grind)
    | (have i₁ := eq2338 X0 X1 X2 (M.op X0 X1) X4 X1
       have i₂ := eq2473 X0 X1 X3
       grind)
    | exact superpose eq2473 eq2338
    | exact resolve eq2338 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq2473
  have eq201381 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op (σ (M.op X3 X3)) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))) = X1 := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq199434 X0 X1 x X3 X4 X5 X6
       have i₂ := eq109 x (σ (M.op X3 X3))
       grind)
    | exact superpose eq109 eq199434
    | exact resolve eq199434 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq199434
  have eq201772 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6)))) = X1 := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq201381 X0 X1 x X4 X5 X6
       have i₂ := eq260 x (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))
       grind)
    | exact superpose eq260 eq201381
    | exact resolve eq201381 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq201381
  have eq3194808 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op (σ y) (σ (M.op y y))) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201772 (σ y) (σ x) X0 X1 X2
       have i₂ := eq16234
       grind)
    | exact superpose eq16234 eq201772
    | exact resolve eq201772 eq16234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16234
  have eq3194822 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3194808 x x x
       have i₂ := eq5081 x x x (σ y) y
       grind)
    | exact superpose eq5081 eq3194808
    | exact resolve eq3194808 eq5081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5081 eq3194808
  have eq3194823 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq3194822
  have eq3195233 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3194823
       grind)
    | exact superpose eq3194823 eq10
    | exact resolve eq10 eq3194823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3194823
  have eq3195580 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3195233
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3195233
    | exact resolve eq3195233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195233
  have eq3217896 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3195580
       grind)
    | exact superpose eq3195580 eq16
    | exact resolve eq16 eq3195580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195580
  have eq3217897 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq3217896
       have r₂ := eq216 x (σ x)
       grind)
    | exact resolve eq3217896 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3217896
  have eq3235964 : ∀ X0 X1 X2 : G, y = (M.op (M.op y (M.op x y)) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201772 y y X0 X1 X2
       have i₂ := eq3217897
       grind)
    | exact superpose eq3217897 eq201772
    | exact resolve eq201772 eq3217897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3217897
  have eq3235967 : x = y := by
    first
    | (have i₁ := eq3235964 x x x
       have i₂ := eq201772 y x x x x
       grind)
    | exact superpose eq201772 eq3235964
    | exact resolve eq3235964 eq201772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201772 eq3235964
  have eq3236037 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3235967
       grind)
    | exact superpose eq3235967 eq16
    | exact resolve eq16 eq3235967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3235967
  have eq3236038 : False := by grind
  exact eq3236038

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  clear eq49
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq85 : x ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y y) := by
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
  have eq86 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq97 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq93
  have eq98 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq97
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq212 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X1 X1)) (M.op (M.op x y) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq541 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq56 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq541 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq541
    | exact resolve eq541 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq687 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X1 (M.op X1 X1) X2
       have i₂ := eq56 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq760 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op X2 X2)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) (σ X0) X2
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq14
    | (have j1 := eq69 X0 X1
       grind)
    | exact resolve eq14 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1788 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1787
    | exact resolve eq1787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq1791 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1788
       have r₂ := eq28
       grind)
    | exact resolve eq1788 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788
  have eq1793 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1791
    | exact resolve eq1791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791
  have eq1829 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1793 eq86
    | (have r₁ := eq86
       have r₂ := eq1793
       grind)
    | exact resolve eq86 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq1793
  have eq1832 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1829
  have eq1833 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1832
  have eq1838 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1833 eq60
    | exact resolve eq60 eq1833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1833
  have eq1845 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq129 eq1838
    | exact resolve eq1838 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1838
  have eq1848 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1845
       have r₂ := eq85
       grind)
    | exact resolve eq1845 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1845
  have eq1852 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1848
       grind)
    | exact superpose eq1848 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1853 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1852
  have eq1855 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1853
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1853
    | exact resolve eq1853 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq1858 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1855
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1855
    | exact resolve eq1855 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq1927 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 X0)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq212 y X0
       have i₂ := eq1858
       grind)
    | exact superpose eq1858 eq212
    | exact resolve eq212 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq1858
  have eq1961 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1927 x
       have i₂ := eq687 sF0 y x
       grind)
    | exact superpose eq687 eq1927
    | exact resolve eq1927 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq1927
  have eq1962 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1961
  have eq1969 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1962 eq30
    | exact resolve eq30 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962
  have eq1988 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1969
    | exact resolve eq1969 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq1989 : x = (M.op x y) ∨ x = y := by grind
  clear eq1988
  have eq1992 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1989 eq21
    | exact resolve eq21 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq2014 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1992
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1992
    | exact resolve eq1992 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq10876 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op y y)) (M.op X0 X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq760 x y X0
       have i₂ := eq1848
       grind)
    | exact superpose eq1848 eq760
    | (have j0 := eq760 x y x
       grind)
    | exact resolve eq760 eq1848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq1848
  have eq11153 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op y y)) (M.op X0 X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10876 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10876
    | (have j0 := eq10876 X0
       grind)
    | exact resolve eq10876 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10876
  have eq11264 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11153 X0
       have i₂ := eq584 y (M.op X0 X0)
       grind)
    | exact superpose eq584 eq11153
    | exact resolve eq11153 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq11153
  have eq11337 : (σ y) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11264 x
       have i₂ := eq541 x sF2
       grind)
    | exact superpose eq541 eq11264
    | exact resolve eq11264 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq11264
  have eq11392 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11337
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11337
    | exact resolve eq11337 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11337
  have eq11393 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11392
  have eq11438 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11393
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11393
    | exact resolve eq11393 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11393
  have eq11480 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11438
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11438
    | exact resolve eq11438 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11438
  have eq11502 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq11480
    | exact resolve eq11480 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11480
  have eq11516 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11502
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11502
    | exact resolve eq11502 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11502
  have eq11521 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11516
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11516
    | exact resolve eq11516 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11516
  have eq11522 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11521
  have eq11531 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11522 eq28
    | exact resolve eq28 eq11522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11522
  have eq11542 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11531
       have r₂ := eq2014
       grind)
    | exact resolve eq11531 eq2014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014 eq11531
  have eq11544 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq11542 eq30
    | exact resolve eq30 eq11542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11542
  have eq11591 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq11544
    | exact resolve eq11544 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11544
  have eq11592 : x = y := by grind
  clear eq11591
  have eq11595 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq11592
       grind)
    | exact superpose eq11592 eq19
    | exact resolve eq19 eq11592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq11596 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq11592
       grind)
    | exact superpose eq11592 eq25
    | exact resolve eq25 eq11592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11592
  have eq11622 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11596
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11596
    | exact resolve eq11596 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11596
  have eq11625 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11622 eq27
    | exact resolve eq27 eq11622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11622
  have eq11758 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11625 eq68
    | exact resolve eq68 eq11625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq11625
  have eq11831 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11758
       have i₂ := eq11595
       grind)
    | exact superpose eq11595 eq11758
    | exact resolve eq11758 eq11595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11595 eq11758
  have eq12410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11831 eq15
    | exact resolve eq15 eq11831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11831
  have eq12451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12410
    | exact resolve eq12410 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq12410
  have eq12460 : False := by grind
  exact eq12460

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pxy_pyx_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq33
    | (have j0 := eq33 X0 X1 x
       grind)
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq69 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op X1 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2
       have i₂ := eq25 X0 X1 (σ X2)
       grind)
    | exact superpose eq25 eq22
    | exact resolve eq22 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq97 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq103 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq89 X0 x X2
       have i₂ := eq97 x X0
       grind)
    | exact superpose eq97 eq89
    | exact resolve eq89 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq97
  have eq247 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq43
    | (have j0 := eq43 X0 X1
       have j1 := eq40 (σ (M.op X0 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq43 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43
  have eq3330 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq247 x y
       grind)
    | exact superpose eq247 eq16
    | (have j1 := eq247 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq247 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq247 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq247 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq3371 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3330
  have eq3952 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) (M.op X0 X0)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq3371
       grind)
    | exact superpose eq3371 eq9
    | exact resolve eq9 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3989 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3952 x
       have i₂ := eq69 x x
       grind)
    | exact superpose eq69 eq3952
    | exact resolve eq3952 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3952
  have eq3990 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3989
  have eq9411 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3990
       grind)
    | exact superpose eq3990 eq10
    | exact resolve eq10 eq3990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3990
  have eq9454 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9411
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9411
    | exact resolve eq9411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9411
  have eq9455 : x = y := by grind
  clear eq9454
  have eq13529 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9455
       grind)
    | exact superpose eq9455 eq16
    | exact resolve eq16 eq9455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9455
  have eq13530 : False := by grind
  exact eq13530

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq66 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ (M.op X0 X0))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq10
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X1 X1) X0
       have i₂ := eq9 X1 X1 X1
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op (M.op X2 X1) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X1 X2 X3 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq24 X0 X0 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq24 X1 X0 X2 X4
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X1 (M.op X1 X1) X2
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25
  have eq134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq159 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134 x y
       grind)
    | exact superpose eq134 eq16
    | (have j1 := eq134 x y
       grind)
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq210 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1
       have i₂ := eq97 (τ X1) X0
       grind)
    | (have i₁ := eq32 X1
       have i₂ := eq97 X0 (τ X1)
       grind)
    | exact superpose eq97 eq32
    | exact resolve eq32 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq97
  have eq252 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq210 X0 (M.op X1 X1)
       grind)
    | exact superpose eq210 eq9
    | exact resolve eq9 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1087 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq159
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq159
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq159
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq159
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq159 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq1088 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by grind
  clear eq1087
  have eq1626 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110 X0 (σ (M.op X0 X0)) X1 X2
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1720 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1626 X0 X1 X2
       have i₂ := eq252 (M.op X0 X0) (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 X2))
       grind)
    | exact superpose eq252 eq1626
    | exact resolve eq1626 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq2356 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))))) X3) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq66 (M.op X0 X0) X3 X4
       have i₂ := eq116 X0 X0 X1 X0 X2
       grind)
    | (have i₁ := eq66 (M.op X0 (M.op X4 X4)) X1 X2
       have i₂ := eq116 X0 X0 X4 X3 X4
       grind)
    | exact superpose eq116 eq66
    | exact resolve eq66 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq2361 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (σ (M.op X4 X4))) (M.op (M.op X5 X3) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq110 X4 X3 X5 (M.op X0 X0)
       have i₂ := eq116 X0 X0 X1 X0 X2
       grind)
    | (have i₁ := eq110 X0 X1 X2 (M.op X0 (M.op X4 X4))
       have i₂ := eq116 X0 X0 X4 X3 X4
       grind)
    | exact superpose eq116 eq110
    | exact resolve eq110 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq2403 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq112 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq116 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq112 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq116 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq116 eq112
    | exact resolve eq112 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq116
  have eq2494 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2403 X0 X1 x X3 x
       have i₂ := eq125 x (M.op X0 X1) x
       grind)
    | exact superpose eq125 eq2403
    | exact resolve eq2403 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq2870 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq117 X0 X1 x x X4 X5
       have i₂ := eq125 x (M.op X0 X1) x
       grind)
    | exact superpose eq125 eq117
    | exact resolve eq117 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq125
  have eq4642 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (σ (M.op X4 X4))) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1720 X4 X3 (M.op X1 X1)
       have i₂ := eq2870 X0 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq2870 eq1720
    | exact resolve eq1720 eq2870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720 eq2870
  have eq17868 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1088
       grind)
    | exact superpose eq1088 eq16
    | exact resolve eq16 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq17869 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17868
       have r₂ := eq210 x (σ x)
       grind)
    | exact resolve eq17868 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17868
  have eq117468 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (σ (M.op (M.op X3 (M.op X4 X4)) (M.op X3 (τ (M.op X0 X0)))))) X1) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2356 X3 X4 (τ X0) X1 X2
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq2356
    | exact resolve eq2356 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2356
  have eq213585 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X2 X2) (σ (M.op X3 X3))) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))) = X1 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2361 X4 X5 X6 (M.op X2 X2) X3 X1
       have i₂ := eq2494 X1 X0 X2
       grind)
    | (have i₁ := eq2361 X0 X1 X2 (M.op X0 X1) X4 X1
       have i₂ := eq2494 X0 X1 X3
       grind)
    | exact superpose eq2494 eq2361
    | exact resolve eq2361 eq2494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361 eq2494
  have eq215524 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op (σ (M.op X3 X3)) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))) = X1 := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq213585 X0 X1 x X3 X4 X5 X6
       have i₂ := eq109 x (σ (M.op X3 X3))
       grind)
    | exact superpose eq109 eq213585
    | exact resolve eq213585 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq213585
  have eq215904 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6)))) = X1 := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq215524 X0 X1 x X4 X5 X6
       have i₂ := eq252 x (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X4 (M.op X5 X5)) (M.op X4 (M.op X6 X6))))
       grind)
    | exact superpose eq252 eq215524
    | exact resolve eq215524 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq215524
  have eq3326366 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (σ x) (σ (M.op y y))) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq215904 (σ x) (σ y) X0 X1 X2
       have i₂ := eq17869
       grind)
    | exact superpose eq17869 eq215904
    | exact resolve eq215904 eq17869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17869 eq215904
  have eq3326403 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3326366 x x x
       have i₂ := eq4642 x x x (σ x) y
       grind)
    | exact superpose eq4642 eq3326366
    | exact resolve eq3326366 eq4642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4642 eq3326366
  have eq3326404 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq3326403
  have eq3326844 : y = (τ (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3326404
       grind)
    | exact superpose eq3326404 eq10
    | exact resolve eq10 eq3326404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326404
  have eq3327238 : x = y ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq3326844
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3326844
    | exact resolve eq3326844 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326844
  have eq3327240 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3327238
       grind)
    | exact superpose eq3327238 eq16
    | exact resolve eq16 eq3327238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327238
  have eq3327241 : (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq3327240
       have r₂ := eq210 x (σ x)
       grind)
    | exact resolve eq3327240 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327240
  have eq3329747 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op y x) (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (τ (M.op X2 X2)))))) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117468 X2 y y X0 X1
       have i₂ := eq3327241
       grind)
    | exact superpose eq3327241 eq117468
    | exact resolve eq117468 eq3327241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327241
  have eq3329780 : x = y := by
    first
    | (have i₁ := eq3329747 x x x
       have i₂ := eq117468 x y x x x
       grind)
    | exact superpose eq117468 eq3329747
    | exact resolve eq3329747 eq117468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117468 eq3329747
  have eq3352248 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3329780
       grind)
    | exact superpose eq3329780 eq16
    | exact resolve eq16 eq3329780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3329780
  have eq3352249 : False := by grind
  exact eq3352249

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq268 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq269 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq269 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq282 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq271 (σ X0)
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq282
    | exact resolve eq282 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq282
  have eq344 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq350 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq344 X0 X1
       have j1 := eq345 X0 X1
       grind)
    | (have r₁ := eq344 X0 X1
       have r₂ := eq345 X0 X1
       grind)
    | exact resolve eq344 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq345
  have eq462 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq350 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq350
    | exact resolve eq350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq350 X1 X0
       grind)
    | exact superpose eq350 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq350 X1 (σ X1)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq350 X0 X1
       grind)
    | exact resolve eq13 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq479 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq475 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq482 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq479 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq479 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq479 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq496 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq462 (τ X0) X1
       grind)
    | exact superpose eq462 eq18
    | (have j1 := eq462 (τ X0) X1
       grind)
    | exact resolve eq18 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq482 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq482
    | exact resolve eq482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq482 X1 X0
       grind)
    | exact superpose eq482 eq22
    | (have j1 := eq482 X1 X0
       grind)
    | exact resolve eq22 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq482
  have eq597 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq546 (τ X0) X1
       grind)
    | exact superpose eq546 eq18
    | (have j1 := eq546 (τ X0) X1
       grind)
    | exact resolve eq18 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq546
  have eq2176 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq496 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq496
    | exact resolve eq496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq2254 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2176 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2176
    | (have j0 := eq2176 X0 X1
       grind)
    | exact resolve eq2176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2432 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq556 X1 (σ X0)
       grind)
    | exact superpose eq556 eq28
    | (have j1 := eq556 X1 (σ X0)
       grind)
    | exact resolve eq28 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq556
  have eq2445 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2432 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2432
    | (have j0 := eq2432 X0 X1
       grind)
    | exact resolve eq2432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2432
  have eq2457 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2445 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2445
    | (have j0 := eq2445 X0 X1
       grind)
    | exact resolve eq2445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2445
  have eq2464 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2457 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2457
    | (have j0 := eq2457 X0 X1
       grind)
    | exact resolve eq2457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq2554 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq2464 X0 X1
       grind)
    | exact superpose eq2464 eq11
    | (have j1 := eq2464 X0 X1
       grind)
    | exact resolve eq11 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464
  have eq2620 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq462 X1 X0
       have i₂ := eq2554 X0 X1
       grind)
    | exact superpose eq2554 eq462
    | (have j0 := eq462 X1 X0
       have j1 := eq2554 X0 X1
       grind)
    | exact resolve eq462 eq2554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq2647 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2620
  have eq2767 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2647 y x
       grind)
    | exact superpose eq2647 eq16
    | (have j1 := eq2647 y x
       grind)
    | exact resolve eq16 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647
  have eq2879 : y = (M.op x y) := by
    first
    | (have j1 := eq2254 x y
       grind)
    | (have r₁ := eq2767
       have r₂ := eq2254 x y
       grind)
    | exact resolve eq2767 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254 eq2767
  have eq3504 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq597 X1 (τ X0)
       grind)
    | exact superpose eq597 eq17
    | (have j1 := eq597 X1 (τ X0)
       grind)
    | exact resolve eq17 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq597
  have eq3513 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3504 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3504
    | (have j0 := eq3504 X0 X1
       grind)
    | exact resolve eq3504 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504
  have eq3524 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3513 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3513
    | (have j0 := eq3513 X0 X1
       grind)
    | exact resolve eq3513 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3513
  have eq3525 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3524 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3524
    | (have j0 := eq3524 X0 X1
       grind)
    | exact resolve eq3524 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524
  have eq3584 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3525 X1 X0
       have i₂ := eq462 X0 X1
       grind)
    | exact superpose eq462 eq3525
    | (have j1 := eq462 X0 X1
       grind)
    | exact resolve eq3525 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq3525
  have eq3629 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3584 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3584
  have eq3802 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3629 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3629
    | (have j0 := eq3629 (σ X0) X1
       grind)
    | exact resolve eq3629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3629
  have eq6594 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x (τ (σ y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3802 x (σ y)
       grind)
    | exact superpose eq3802 eq16
    | (have j1 := eq3802 x (σ y)
       grind)
    | exact resolve eq16 eq3802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802
  have eq6723 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x (τ (σ y)))) := by
    first
    | (have i₁ := eq6594
       have i₂ := eq2879
       grind)
    | exact superpose eq2879 eq6594
    | exact resolve eq6594 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2879 eq6594
  have eq6724 : (M.op (σ x) (σ y)) = (σ (M.op x (τ (σ y)))) := by grind
  clear eq6723
  have eq6743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6724
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6724
    | exact resolve eq6724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6724
  have eq6750 : False := by grind
  exact eq6750
