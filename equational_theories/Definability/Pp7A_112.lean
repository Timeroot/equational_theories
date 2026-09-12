import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq75
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq75 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by
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
  have eq97 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq115 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq115 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq115 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq115 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq121 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq116 sF2
       grind)
    | exact superpose eq116 eq49
    | exact resolve eq49 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq122 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq121
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq121
    | exact resolve eq121 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq121
  have eq1988 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq14
    | exact resolve eq14 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2007 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1988 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq1988
    | exact resolve eq1988 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988
  have eq2025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2007 eq69
    | (have j0 := eq69 (σ y) (σ x)
       grind)
    | exact resolve eq69 eq2007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2007
  have eq2026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq2025
    | exact resolve eq2025 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq2029 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq2026
       have r₂ := eq27
       grind)
    | exact resolve eq2026 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2026
  have eq2041 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op (σ y) (σ x)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2029 eq14
    | exact resolve eq14 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029
  have eq2060 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2041 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq2041
    | exact resolve eq2041 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041
  have eq2078 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2060 eq29
    | exact resolve eq29 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2060
  have eq2104 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq2078
    | exact resolve eq2078 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2078
  have eq2105 : x = y := by grind
  clear eq2104
  have eq2108 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2105
       grind)
    | exact superpose eq2105 eq18
    | exact resolve eq18 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2109 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2105
       grind)
    | exact superpose eq2105 eq24
    | exact resolve eq24 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2105
  have eq2146 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2109
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2109
    | exact resolve eq2109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2109
  have eq2151 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2146 eq26
    | exact resolve eq26 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2146
  have eq2216 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2151 eq122
    | exact resolve eq122 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq2151
  have eq2247 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2216
       have i₂ := eq2108
       grind)
    | exact superpose eq2108 eq2216
    | exact resolve eq2216 eq2108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108 eq2216
  have eq2252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2247 eq15
    | exact resolve eq15 eq2247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq2278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2252
    | exact resolve eq2252 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2252
  have eq2283 : False := by grind
  exact eq2283

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq44 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq49 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq52 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq52
    | exact resolve eq52 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq52
  have eq76 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X1) = X2 ∨ (M.op X1 X1) = (k X1 X2) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X1) = X2 ∨ (M.op X1 X1) = (k X1 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq78 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq78 X0 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq76 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq76 X0 X1 X2
       have r₂ := eq12 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq76 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq76 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq222 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq10
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq262 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq24 X2 X0 X1 x
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq24 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op X1 (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X1) X2) X1 X3
       have i₂ := eq24 X2 X1 X4 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq262 X1 X2 (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0))
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq262
    | exact resolve eq262 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq262 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0))
       have i₂ := eq262 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq262 eq262
    | exact resolve eq262 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X2 (M.op (M.op X3 X2) X0)) X2 X4 X1
       have i₂ := eq262 X2 X3 X0
       grind)
    | exact superpose eq262 eq24
    | exact resolve eq24 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq446 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X3 X2) X0) X2 x
       grind)
    | exact superpose eq9 eq446
    | exact resolve eq446 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq486 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X2))) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X2 X2) X0 x X1
       have i₂ := eq85 X2 X0 x
       grind)
    | exact superpose eq85 eq24
    | (have j1 := eq85 X2 X0 X2
       grind)
    | exact resolve eq24 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq616 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X4 (M.op X2 (M.op X2 X0))) X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq24 X3 (M.op X2 (M.op X2 X0)) X4 (M.op x X2)
       have i₂ := eq273 x X2 X0
       grind)
    | exact superpose eq273 eq24
    | exact resolve eq24 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq622 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) = (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq616 X0 X2 X3 x
       have i₂ := eq437 X3 (M.op X2 X0) X2 x
       grind)
    | exact superpose eq437 eq616
    | exact resolve eq616 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq842 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) = (M.op (M.op X5 (M.op X3 X1)) (M.op (M.op X3 X1) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X4 (M.op X3 X1) X2 X5
       have i₂ := eq452 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X1 X0
       grind)
    | (have i₁ := eq24 X4 (M.op X3 X1) X2 X5
       have i₂ := eq452 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X1 X3
       grind)
    | exact superpose eq452 eq24
    | exact resolve eq24 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq452
  have eq865 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) = (M.op X1 (M.op X1 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq842 X0 X1 X2 X3 X4 x
       have i₂ := eq433 X4 X1 X3 x
       grind)
    | exact superpose eq433 eq842
    | exact resolve eq842 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq842
  have eq3135 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq83 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq3136 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3135 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq3135 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq3135 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq3265 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3136 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136
  have eq3911 : ∀ X0 X1 : G, (M.op X1 (τ X0)) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3265 (τ X0) X1
       have i₂ := eq222 X0
       grind)
    | exact superpose eq222 eq3265
    | (have j0 := eq3265 (τ X0) X1
       grind)
    | exact resolve eq3265 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3265
  have eq9535 : ∀ X0 X2 X3 X4 X5 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op X2 X2)) (M.op (M.op X4 (M.op X0 (M.op X2 X2))) (M.op (M.op X5 (M.op X0 (M.op X2 X2))) (M.op (M.op X0 (M.op X2 X2)) X3)))) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq275 X5 (M.op X0 (M.op X2 X2)) X3 X4 (M.op x X0)
       have i₂ := eq486 X0 x X2
       grind)
    | exact superpose eq486 eq275
    | (have j1 := eq486 X0 x X2
       grind)
    | exact resolve eq275 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq486
  have eq10273 : ∀ X0 X2 X3 X5 : G, (M.op X0 X3) = (M.op (M.op X2 X2) (M.op (M.op X2 X2) (M.op (M.op X5 (M.op X0 (M.op X2 X2))) (M.op (M.op X0 (M.op X2 X2)) X3)))) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2 X3 X5
    first
    | (have i₁ := eq9535 X0 X2 X3 x X5
       have i₂ := eq437 (M.op (M.op X5 (M.op X0 (M.op X2 X2))) (M.op (M.op X0 (M.op X2 X2)) X3)) (M.op X2 X2) X0 x
       grind)
    | exact superpose eq437 eq9535
    | (have j0 := eq9535 X0 X2 X3 x X5
       grind)
    | exact resolve eq9535 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq9535
  have eq10394 : ∀ X0 X2 X3 X5 : G, (M.op X0 X3) = (M.op X2 (M.op (M.op X2 (M.op X2 X2)) (M.op (M.op X5 (M.op X0 (M.op X2 X2))) (M.op (M.op X0 (M.op X2 X2)) X3)))) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2 X3 X5
    first
    | (have i₁ := eq10273 X0 X2 X3 X5
       have i₂ := eq622 X2 X2 (M.op (M.op X5 (M.op X0 (M.op X2 X2))) (M.op (M.op X0 (M.op X2 X2)) X3))
       grind)
    | exact superpose eq622 eq10273
    | (have j0 := eq10273 X0 X2 X3 X5
       grind)
    | exact resolve eq10273 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq10273
  have eq10456 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op X2 (M.op (M.op X2 X2) (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X2 X2)) X3)))) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq10394 X0 X2 X3 x
       have i₂ := eq865 X2 (M.op X2 X2) x X0 (M.op (M.op X0 (M.op X2 X2)) X3)
       grind)
    | exact superpose eq865 eq10394
    | (have j0 := eq10394 X0 X2 X3 x
       grind)
    | exact resolve eq10394 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq10394
  have eq10493 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op X2 X3) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq10456 X0 X2 X3
       have i₂ := eq262 (M.op X2 X2) X0 X3
       grind)
    | exact superpose eq262 eq10456
    | (have j0 := eq10456 X0 X2 X3
       grind)
    | exact resolve eq10456 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq10456
  have eq11071 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq222 X1
       have i₂ := eq10493 X0 (τ X1) (τ X1)
       grind)
    | (have i₁ := eq222 X0
       have i₂ := eq10493 (τ X0) x (τ X0)
       grind)
    | exact superpose eq10493 eq222
    | (have j1 := eq10493 X0 (τ X1) x
       grind)
    | exact resolve eq222 eq10493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq10493
  have eq11117 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq11071 X0 X1
       have j1 := eq3911 X1 X0
       grind)
    | (have r₁ := eq11071 X1 X0
       have r₂ := eq3911 X0 X1
       grind)
    | exact resolve eq11071 eq3911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3911 eq11071
  have eq11688 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11117 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11117
    | exact resolve eq11117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11117
  have eq12160 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq11688 (σ X1) (σ X0)
       grind)
    | exact superpose eq11688 eq15
    | exact resolve eq15 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12181 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12160 X0 X1
       have i₂ := eq11688 X1 X0
       grind)
    | exact superpose eq11688 eq12160
    | exact resolve eq12160 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11688 eq12160
  have eq15448 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12181 x y
       grind)
    | exact superpose eq12181 eq16
    | (have r₁ := eq16
       have r₂ := eq12181 x y
       grind)
    | exact resolve eq16 eq12181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12181
  have eq15577 : False := by grind
  exact eq15577

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X1 X0)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq64 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq86 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq63 X2 X0 X1 x
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq63 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op X1 (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X1) X2) X1 X3
       have i₂ := eq63 X2 X1 X4 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq86 X1 X2 (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0))
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq86 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0))
       have i₂ := eq86 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq86 eq86
    | exact resolve eq86 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X2 (M.op (M.op X3 X2) X0)) X2 X4 X1
       have i₂ := eq86 X2 X3 X0
       grind)
    | exact superpose eq86 eq63
    | exact resolve eq63 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X3 X2) X0) X2 x
       grind)
    | exact superpose eq9 eq112
    | exact resolve eq112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq163 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op (M.op X2 (M.op X2 X0)) X3)) = (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X3 (M.op X2 (M.op X2 X0)) (M.op x X2) X1
       have i₂ := eq93 x X2 X0
       grind)
    | exact superpose eq93 eq63
    | exact resolve eq63 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X4 (M.op X2 (M.op X2 X0))) X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq63 X3 (M.op X2 (M.op X2 X0)) X4 (M.op x X2)
       have i₂ := eq93 x X2 X0
       grind)
    | exact superpose eq93 eq63
    | exact resolve eq63 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq165 X0 X2 X3 x
       have i₂ := eq106 X3 (M.op X2 X0) X2 x
       grind)
    | exact superpose eq106 eq165
    | exact resolve eq165 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq165
  have eq170 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq163 X0 x X2 X3
       have i₂ := eq104 X3 (M.op X2 X0) X2 x
       grind)
    | exact superpose eq104 eq163
    | exact resolve eq163 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq182 : ∀ X0 X2 X3 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq170 X0 X2 X3
       have i₂ := eq168 X0 X2 X3
       grind)
    | exact superpose eq168 eq170
    | exact resolve eq170 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq216 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X0))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq116 X4 X1 (M.op (M.op X2 X3) (M.op X3 X0)) X3
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq116
    | exact resolve eq116 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq116 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
       have i₂ := eq93 x X2 X0
       grind)
    | exact superpose eq93 eq116
    | exact resolve eq116 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) = (M.op (M.op X5 (M.op X3 X1)) (M.op (M.op X3 X1) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq63 X4 (M.op X3 X1) X2 X5
       have i₂ := eq116 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X1 X0
       grind)
    | (have i₁ := eq63 X4 (M.op X3 X1) X2 X5
       have i₂ := eq116 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X1 X3
       grind)
    | exact superpose eq116 eq63
    | exact resolve eq63 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X4)) = (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq275 X0 X1 X2 X3 X4 x
       have i₂ := eq104 X4 X1 X3 x
       grind)
    | exact superpose eq104 eq275
    | exact resolve eq275 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq275
  have eq317 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq65 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq65
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq331 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) ∨ (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq14 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq14 X0 (M.op (M.op x X1) (M.op X1 X0))
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 (M.op X1 X1) X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq331 X0 X1
       have j1 := eq12 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq331 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq331 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq331 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq351 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq322 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq322 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq322 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq356 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq317 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq317 X0 X1 X2
       have r₂ := eq12 (M.op (M.op X2 X1) X0) X1
       grind)
    | (have r₁ := eq317 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq317 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq1998 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq351 X1 X0
       have i₂ := eq342 X0 X1
       grind)
    | exact superpose eq342 eq351
    | (have j0 := eq351 X1 X0
       have j1 := eq342 (M.op X1 X1) X0
       grind)
    | exact resolve eq351 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq351
  have eq2011 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1998 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1998 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq1998 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1998 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998
  have eq2053 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X1 X0 X0
       have i₂ := eq2011 X0 X0
       grind)
    | exact superpose eq2011 eq93
    | (have j1 := eq2011 X0 X0
       grind)
    | exact resolve eq93 eq2011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2090 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq2011 (M.op X0 X1) X1
       grind)
    | exact superpose eq2011 eq9
    | (have j1 := eq2011 (M.op X0 X1) X1
       grind)
    | exact resolve eq9 eq2011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2124 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2090 X0 X1
       have j1 := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq2090 X0 X1
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact resolve eq2090 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2230 : ∀ X0 X2 : G, (M.op X0 X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq86 X0 x X2
       have i₂ := eq356 X2 X0 x
       grind)
    | exact superpose eq356 eq86
    | (have j1 := eq356 X2 X0 X2
       grind)
    | exact resolve eq86 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq2686 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2124 (M.op x X0) X0
       have i₂ := eq2053 X0 x
       grind)
    | exact superpose eq2053 eq2124
    | (have j1 := eq2053 X0 x
       grind)
    | exact resolve eq2124 eq2053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053
  have eq2715 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2686 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686
  have eq2798 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2715 (σ X0)
       grind)
    | exact superpose eq2715 eq15
    | exact resolve eq15 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2817 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2798 X0
       have i₂ := eq2715 X0
       grind)
    | exact superpose eq2715 eq2798
    | exact resolve eq2798 eq2715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2715 eq2798
  have eq2995 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2230 (σ X0) X1
       have i₂ := eq2817 X0
       grind)
    | exact superpose eq2817 eq2230
    | (have j0 := eq2230 (σ X0) X1
       grind)
    | exact resolve eq2230 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2996 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq2817 X0
       grind)
    | exact superpose eq2817 eq9
    | exact resolve eq9 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2997 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq2817 X0
       grind)
    | exact superpose eq2817 eq9
    | exact resolve eq9 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3008 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86 (σ X0) (σ X0) X1
       have i₂ := eq2817 X0
       grind)
    | exact superpose eq2817 eq86
    | exact resolve eq86 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3011 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X1 (σ X0) (σ X0)
       have i₂ := eq2817 X0
       grind)
    | exact superpose eq2817 eq93
    | exact resolve eq93 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3013 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (M.op X1 (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 X2 X1 (σ X0) (σ X0)
       have i₂ := eq2817 X0
       grind)
    | exact superpose eq2817 eq116
    | exact resolve eq116 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3018 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (M.op (M.op X2 (M.op (σ X0) (σ (M.op X0 X0)))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220 (σ X0) X2 (σ X0) X1
       have i₂ := eq2817 X0
       grind)
    | exact superpose eq2817 eq220
    | exact resolve eq220 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq3022 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2124 (σ X0) (σ X0)
       have i₂ := eq2817 X0
       grind)
    | exact superpose eq2817 eq2124
    | exact resolve eq2124 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3023 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3022 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq3022
    | exact resolve eq3022 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022
  have eq3029 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3023 X0
       have i₂ := eq2124 X0 X0
       grind)
    | exact superpose eq2124 eq3023
    | exact resolve eq3023 eq2124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023
  have eq3033 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3011 X0 X1
       have i₂ := eq3029 X0
       grind)
    | exact superpose eq3029 eq3011
    | exact resolve eq3011 eq3029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3035 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (M.op (M.op X2 (σ (M.op X0 (M.op X0 X0)))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3018 X0 X1 X2
       have i₂ := eq3029 X0
       grind)
    | exact superpose eq3029 eq3018
    | exact resolve eq3018 eq3029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018
  have eq4908 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq2996 X0 (σ X0)
       have i₂ := eq2817 X0
       grind)
    | exact superpose eq2817 eq2996
    | exact resolve eq2996 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq4954 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4908 X0
       have i₂ := eq2817 (M.op X0 X0)
       grind)
    | exact superpose eq2817 eq4908
    | exact resolve eq4908 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817 eq4908
  have eq5199 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) X2) = (M.op (σ (M.op X0 (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 X2 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq3029 X0
       grind)
    | exact superpose eq3029 eq116
    | exact resolve eq116 eq3029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5209 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) = (k (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2124 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq3029 X0
       grind)
    | exact superpose eq3029 eq2124
    | exact resolve eq2124 eq3029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5212 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) = (σ (k (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5209 X0
       have i₂ := eq15 (M.op X0 (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq15 eq5209
    | exact resolve eq5209 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5209
  have eq5241 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) = (σ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5212 X0
       have i₂ := eq2124 X0 (M.op X0 X0)
       grind)
    | exact superpose eq2124 eq5212
    | exact resolve eq5212 eq2124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124 eq5212
  have eq5258 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5241 X0
       have i₂ := eq93 X0 X0 X0
       grind)
    | exact superpose eq93 eq5241
    | exact resolve eq5241 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5241
  have eq5815 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4954 X1
       have i₂ := eq116 (M.op X1 X1) X1 X1 X0
       grind)
    | (have i₁ := eq4954 X1
       have i₂ := eq116 (M.op X1 X1) X0 X1 X1
       grind)
    | exact superpose eq116 eq4954
    | exact resolve eq4954 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4954
  have eq9457 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq2995 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq2995 X0 (σ X0)
       grind)
    | exact superpose eq2995 eq10
    | (have j1 := eq2995 X1 X0
       grind)
    | exact resolve eq10 eq2995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995
  have eq10194 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (M.op (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) X2)) = (M.op (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) (M.op (M.op X3 (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X2 (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) X3 (σ X0)
       have i₂ := eq2997 X0 X1
       grind)
    | exact superpose eq2997 eq63
    | exact resolve eq63 eq2997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997
  have eq10245 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) X2)) = (M.op (σ X0) (M.op (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10194 X0 X1 X2 x
       have i₂ := eq281 (M.op X1 (σ X0)) (σ (M.op X0 X0)) x (M.op X1 (σ X0)) X2
       grind)
    | exact superpose eq281 eq10194
    | exact resolve eq10194 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq10194
  have eq10292 : ∀ X0 X2 : G, (M.op (σ X0) (M.op (σ (M.op X0 (M.op X0 X0))) X2)) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq10245 X0 x X2
       have i₂ := eq5199 X0 (M.op x (σ X0)) X2
       grind)
    | exact superpose eq5199 eq10245
    | exact resolve eq10245 eq5199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5199 eq10245
  have eq12848 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq9457 (σ X0) X1
       grind)
    | exact superpose eq9457 eq15
    | (have j1 := eq9457 (σ X0) X1
       grind)
    | exact resolve eq15 eq9457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9457
  have eq12862 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12848 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12848
    | (have j0 := eq12848 X0 X1
       grind)
    | exact resolve eq12848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12848
  have eq14437 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12862 X0 X1
       have i₂ := eq2230 X1 X0
       grind)
    | exact superpose eq2230 eq12862
    | (have j0 := eq12862 X0 X1
       have j1 := eq2230 X1 X0
       grind)
    | exact resolve eq12862 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230 eq12862
  have eq14644 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14437 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14437
  have eq19438 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14644 x y
       grind)
    | exact superpose eq14644 eq16
    | (have j1 := eq14644 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq14644 x y
       grind)
    | exact resolve eq16 eq14644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14644
  have eq19714 : x = (M.op y y) := by grind
  clear eq19438
  have eq19941 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3008 y X0
       have i₂ := eq19714
       grind)
    | exact superpose eq19714 eq3008
    | exact resolve eq3008 eq19714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008
  have eq19943 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq3029 y
       have i₂ := eq19714
       grind)
    | exact superpose eq19714 eq3029
    | exact resolve eq3029 eq19714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3029
  have eq19945 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (σ (M.op y x))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3035 y X0 X1
       have i₂ := eq19714
       grind)
    | exact superpose eq19714 eq3035
    | exact resolve eq3035 eq19714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq19950 : (σ y) = (M.op (σ x) (σ (M.op y x))) := by
    first
    | (have i₁ := eq5258 y
       have i₂ := eq19714
       grind)
    | exact superpose eq19714 eq5258
    | exact resolve eq5258 eq19714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5258
  have eq19979 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq93 X0 y y
       have i₂ := eq19714
       grind)
    | exact superpose eq19714 eq93
    | exact resolve eq93 eq19714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq19984 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X0 y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X1 X0 y y
       have i₂ := eq19714
       grind)
    | exact superpose eq19714 eq116
    | exact resolve eq116 eq19714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq19986 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op X1 (M.op (M.op X2 y) x)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216 y X1 X2 y X0
       have i₂ := eq19714
       grind)
    | exact superpose eq19714 eq216
    | exact resolve eq216 eq19714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq19999 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq5815 y y
       have i₂ := eq19714
       grind)
    | exact superpose eq19714 eq5815
    | exact resolve eq5815 eq19714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5815 eq19714
  have eq20097 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 (M.op x x)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19986 X0 X1 x
       have i₂ := eq19984 x x
       grind)
    | exact superpose eq19984 eq19986
    | exact resolve eq19986 eq19984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19986
  have eq20119 : y = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq19979 x
       have i₂ := eq19984 x (M.op y x)
       grind)
    | exact superpose eq19984 eq19979
    | exact resolve eq19979 eq19984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19979 eq19984
  have eq21670 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ (M.op y x)) X0) := by
    intro X0
    first
    | (have i₁ := eq3013 x (σ y) X0
       have i₂ := eq19943
       grind)
    | exact superpose eq19943 eq3013
    | exact resolve eq3013 eq19943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3013 eq19943
  have eq21974 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ (M.op y x)) X0)) = (M.op (σ (M.op y x)) (M.op (M.op X1 (σ (M.op y x))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ (M.op y x)) X1 (σ x)
       have i₂ := eq19950
       grind)
    | exact superpose eq19950 eq63
    | exact resolve eq63 eq19950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq21981 : ∀ X0 : G, (M.op (σ (M.op y x)) (M.op (σ (M.op y x)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq86 (σ (M.op y x)) (σ x) X0
       have i₂ := eq19950
       grind)
    | exact superpose eq19950 eq86
    | exact resolve eq86 eq19950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq21987 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ (M.op y x))) X1) = (M.op (σ (M.op y x)) (M.op (σ y) (M.op (M.op X2 (σ (M.op y x))) (M.op (σ (M.op y x)) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X2 (σ (M.op y x)) X1 (σ x) X0
       have i₂ := eq19950
       grind)
    | exact superpose eq19950 eq95
    | exact resolve eq95 eq19950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq19950
  have eq22022 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ (M.op y x))) X1) = (M.op (σ (M.op x x)) (M.op (σ y) (M.op (M.op X2 (σ (M.op y x))) (M.op (σ (M.op y x)) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21987 X0 X1 X2
       have i₂ := eq21670 (M.op (σ y) (M.op (M.op X2 (σ (M.op y x))) (M.op (σ (M.op y x)) X1)))
       grind)
    | exact superpose eq21670 eq21987
    | exact resolve eq21987 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21987
  have eq22026 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op (σ (M.op y x)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21981 X0
       have i₂ := eq21670 (M.op (σ (M.op y x)) (M.op (σ y) X0))
       grind)
    | exact superpose eq21670 eq21981
    | exact resolve eq21981 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21981
  have eq22030 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ (M.op y x)) X0)) = (M.op (σ (M.op x x)) (M.op (M.op X1 (σ (M.op y x))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21974 X0 X1
       have i₂ := eq21670 (M.op (M.op X1 (σ (M.op y x))) X0)
       grind)
    | exact superpose eq21670 eq21974
    | exact resolve eq21974 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21974
  have eq22051 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op y x))) X1) = (M.op (σ (M.op x x)) (M.op (σ y) (M.op (σ y) (M.op (σ (M.op y x)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22022 X0 X1 x
       have i₂ := eq19945 (M.op (σ (M.op y x)) X1) x
       grind)
    | exact superpose eq19945 eq22022
    | exact resolve eq22022 eq19945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22022
  have eq22054 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op (σ (M.op x x)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22026 X0
       have i₂ := eq21670 (M.op (σ y) X0)
       grind)
    | exact superpose eq21670 eq22026
    | exact resolve eq22026 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22026
  have eq22058 : ∀ X0 : G, (M.op (σ y) (M.op (σ (M.op y x)) X0)) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq22030 X0 x
       have i₂ := eq19945 X0 x
       grind)
    | exact superpose eq19945 eq22030
    | exact resolve eq22030 eq19945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22030
  have eq22072 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op y x))) X1) = (M.op (σ (M.op x x)) (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x x)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22051 X0 X1
       have i₂ := eq21670 X1
       grind)
    | exact superpose eq21670 eq22051
    | exact resolve eq22051 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22051
  have eq22075 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x (M.op x x))) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22054 X0
       have i₂ := eq10292 x (M.op (σ y) X0)
       grind)
    | exact superpose eq10292 eq22054
    | exact resolve eq22054 eq10292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22054
  have eq22076 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ (M.op x x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq22058 X0
       have i₂ := eq21670 X0
       grind)
    | exact superpose eq21670 eq22058
    | exact resolve eq22058 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21670 eq22058
  have eq22079 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (M.op x x)) (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x x)) X1)))) := by
    intro X1
    first
    | (have i₁ := eq22072 x X1
       have i₂ := eq19945 X1 x
       grind)
    | exact superpose eq19945 eq22072
    | exact resolve eq22072 eq19945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19945 eq22072
  have eq22087 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ (M.op x x)) (M.op (σ y) (M.op (σ (M.op x x)) X1)))) := by
    intro X1
    first
    | (have i₁ := eq22079 X1
       have i₂ := eq22076 (M.op (σ y) (M.op (σ (M.op x x)) X1))
       grind)
    | exact superpose eq22076 eq22079
    | exact resolve eq22079 eq22076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22079
  have eq22091 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x x)) (M.op (σ (M.op x x)) X1)))) := by
    intro X1
    first
    | (have i₁ := eq22087 X1
       have i₂ := eq22076 (M.op (σ (M.op x x)) X1)
       grind)
    | exact superpose eq22076 eq22087
    | exact resolve eq22087 eq22076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22076 eq22087
  have eq22093 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (M.op (σ (M.op x (M.op x x))) X1)))) := by
    intro X1
    first
    | (have i₁ := eq22091 X1
       have i₂ := eq10292 x X1
       grind)
    | exact superpose eq10292 eq22091
    | exact resolve eq22091 eq10292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10292 eq22091
  have eq22095 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (M.op x (M.op x x))) X1) := by
    intro X1
    first
    | (have i₁ := eq22093 X1
       have i₂ := eq19941 (M.op (σ (M.op x (M.op x x))) X1)
       grind)
    | exact superpose eq19941 eq22093
    | exact resolve eq22093 eq19941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19941 eq22093
  have eq22098 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22075 X0
       have i₂ := eq22095 (M.op (σ y) X0)
       grind)
    | exact superpose eq22095 eq22075
    | exact resolve eq22075 eq22095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22075 eq22095
  have eq22289 : (σ (M.op x x)) = (M.op (σ y) (σ (M.op (M.op x x) (M.op (M.op x x) (M.op x x))))) := by
    first
    | (have i₁ := eq3033 (M.op x x) (σ y)
       have i₂ := eq19999
       grind)
    | exact superpose eq19999 eq3033
    | exact resolve eq3033 eq19999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3033
  have eq22363 : (σ (M.op x x)) = (M.op (σ y) (σ (M.op x (M.op (M.op x (M.op x x)) (M.op x x))))) := by
    first
    | (have i₁ := eq22289
       have i₂ := eq168 x x (M.op x x)
       grind)
    | exact superpose eq168 eq22289
    | exact resolve eq22289 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq22289
  have eq22399 : (σ (M.op x x)) = (M.op (σ y) (σ (M.op x (M.op x (M.op (M.op x (M.op x x)) x))))) := by
    first
    | (have i₁ := eq22363
       have i₂ := eq182 x x x
       grind)
    | exact superpose eq182 eq22363
    | exact resolve eq22363 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq22363
  have eq22418 : (σ (M.op x x)) = (M.op (σ y) (σ (M.op x (M.op x (M.op y x))))) := by
    first
    | (have i₁ := eq22399
       have i₂ := eq20097 x x
       grind)
    | exact superpose eq20097 eq22399
    | exact resolve eq22399 eq20097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20097 eq22399
  have eq22431 : (σ (M.op x x)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22418
       have i₂ := eq20119
       grind)
    | exact superpose eq20119 eq22418
    | exact resolve eq22418 eq20119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20119 eq22418
  have eq26888 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq22098 (σ (M.op x y))
       have i₂ := eq22431
       grind)
    | exact superpose eq22431 eq22098
    | exact resolve eq22098 eq22431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22098 eq22431
  have eq26965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26888
       have i₂ := eq19999
       grind)
    | exact superpose eq19999 eq26888
    | exact resolve eq26888 eq19999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19999 eq26888
  have eq27001 : False := by grind
  exact eq27001

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq19 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq21 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : (M.op x y) = (M.op x y) := by grind
  have eq25 : (M.op x y) = (M.op x y) := by grind
  clear eq24
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq27 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq26
  have eq28 : (σ x) = (σ x) := by grind
  have eq29 : (σ x) = (σ x) := by grind
  clear eq28
  have eq30 : (σ y) = (σ y) := by grind
  have eq31 : (σ y) = (σ y) := by grind
  clear eq30
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq33 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq32
  have eq34 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq19
    | (have j1 := eq20 X0
       grind)
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq36 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq23 eq22
    | (have j1 := eq23 X0
       grind)
    | exact resolve eq22 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq42 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq25
    | exact resolve eq25 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq39
  have eq43 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq41
       grind)
    | exact superpose eq41 eq42
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq48 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (τ X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq47
    | exact resolve eq47 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (τ (σ y)) (M.op (M.op x y) (M.op (τ (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq33 eq9
    | (have j0 := eq9 X0 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq33 eq9
    | (have j0 := eq9 (σ y) (σ x) X0
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X1 X0)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (M.op x y) ≠ (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq43 eq12
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq33 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 : G, (k (M.op (M.op X2 X1) (M.op X1 X0)) X1) = X0 ∨ (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X2 X1) (M.op X1 X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X1) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq14
    | (have j0 := eq14 (M.op (M.op X2 X1) (M.op X1 X0)) X1
       grind)
    | exact resolve eq14 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq43 eq14
    | (have j0 := eq14 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X2 X0) (M.op X0 X1)) ∨ (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 (k (M.op X0 X1) (M.op X2 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 (M.op X0 X1) (M.op X2 X0)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 (M.op X0 X1) (M.op X2 X0)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq111
       have r₂ := eq88
       grind)
    | exact resolve eq111 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq111
  have eq128 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have r₁ := eq109
       have r₂ := eq86
       grind)
    | exact resolve eq109 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq109
  have eq129 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X2 X1) (M.op X1 X0))) = X1 ∨ (k (M.op (M.op X2 X1) (M.op X1 X0)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq108 X0 X1 X2
       have j1 := eq85 X0 X1 X2
       grind)
    | (have r₁ := eq108 X1 X1 X2
       have r₂ := eq85 (k (M.op (M.op X2 X1) (M.op X1 X1)) X1) X1 X2
       grind)
    | (have r₁ := eq108 X0 X1 X2
       have r₂ := eq85 X0 (k (M.op (M.op X2 X1) (M.op X1 X0)) X1) X2
       grind)
    | (have r₁ := eq108 X0 X1 X2
       have r₂ := eq85 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X2 X1) (M.op X1 X0))) X1 X2
       grind)
    | exact resolve eq108 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq148 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq48
    | exact resolve eq48 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq220 : ∀ X0 : G, (M.op (M.op x y) (M.op (τ (σ y)) X0)) = (M.op (τ (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq66 eq66
    | exact resolve eq66 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op X1 (σ y)) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (M.op (M.op x sF5) (M.op sF5 X0))
       have i₂ := eq9 X0 sF5 x
       grind)
    | exact superpose eq9 eq66
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op X1 (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (M.op (M.op x y) (M.op (τ (σ y)) (M.op (τ (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq220 eq64
    | exact resolve eq64 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq126 eq34
    | exact resolve eq34 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq372 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq85 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X4 (M.op (M.op X2 X1) (M.op X1 X0))) X3)) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq67 X3 (M.op (M.op X2 X1) (M.op X1 X0)) X4 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq67 X2 X0 X1 x
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq67 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op X1 (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X1) X2) X1 X3
       have i₂ := eq67 X2 X1 X4 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (τ (σ y))) X1) = (M.op (M.op x y) (M.op (τ (σ y)) (M.op (M.op X0 (τ (σ y))) (M.op (τ (σ y)) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq263 (M.op (M.op X2 (τ sF5)) X0)
       have i₂ := eq67 X0 (τ sF5) X2 x
       grind)
    | exact superpose eq67 eq263
    | exact resolve eq263 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq465 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ y)) X1) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ y) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (M.op (M.op X2 sF5) X0)
       have i₂ := eq67 X0 sF5 X2 x
       grind)
    | exact superpose eq67 eq66
    | exact resolve eq66 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X1 X2 : G, (M.op (M.op X2 (σ y)) X1) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X1)))) := by
    intro X1 X2
    first
    | exact superpose eq233 eq465
    | exact resolve eq465 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq468 : ∀ X1 X2 : G, (M.op (M.op x y) X1) = (M.op (M.op X2 (τ (σ y))) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq461 X2 x X2
       have i₂ := eq9 x (τ sF5) X2
       grind)
    | exact superpose eq9 eq461
    | exact resolve eq461 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq480 : ∀ X1 X2 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op X2 (σ y)) X1) := by
    intro X1 X2
    first
    | exact superpose eq66 eq466
    | exact resolve eq466 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq694 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op (M.op X5 (M.op (M.op X2 X3) (M.op X3 X4))) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq67 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) (M.op (M.op X2 X3) (M.op X3 X4)) X5 X1
       have i₂ := eq63 X4 X2 X3 X0
       grind)
    | exact superpose eq63 eq67
    | exact resolve eq67 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq694 X0 X1 X2 X3 X4 x
       have i₂ := eq395 X4 X3 X2 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) x
       grind)
    | exact superpose eq395 eq694
    | exact resolve eq694 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq694
  have eq713 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq696 X0 X1 X2 X3 X4
       have i₂ := eq63 X4 X2 X3 X0
       grind)
    | exact superpose eq63 eq696
    | exact resolve eq696 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq696
  have eq767 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (τ (σ x)) X0) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq128 eq468
    | exact resolve eq468 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : (τ (σ x)) ≠ (τ (σ y)) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq128 eq12
    | exact resolve eq12 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq128 eq14
    | exact resolve eq14 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq778 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq772
  have eq784 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have r₁ := eq771
       have r₂ := eq778
       grind)
    | exact resolve eq771 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq778
  have eq1094 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq784 eq15
    | exact resolve eq15 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq1098 : (σ (τ (σ x))) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq1094
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq1094
    | exact resolve eq1094 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1100 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1098
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq1098
    | exact resolve eq1098 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1105 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1100 eq15
    | exact resolve eq15 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1106 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1105
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq1105
    | exact resolve eq1105 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1106
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq1106
    | exact resolve eq1106 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1109 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq1108
    | exact resolve eq1108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1141 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq1109 eq112
    | (have j0 := eq112 (σ y) (σ y) x
       grind)
    | exact resolve eq112 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1146 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1148 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq240 eq1146
    | exact resolve eq1146 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1150 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq232 eq1148
    | exact resolve eq1148 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1338 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) = (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) ∨ (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X2 := by
    intro X0 X1 X2
    grind
  have eq1341 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) ≠ X0 ∨ (k (M.op (M.op X1 X0) (M.op X0 X2)) (M.op (M.op X1 X0) (M.op X0 X2))) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X2 X1) (M.op X1 X0))
       have i₂ := eq129 X0 X1 X2
       grind)
    | exact superpose eq129 eq12
    | (have j1 := eq129 X2 X0 X1
       grind)
    | exact resolve eq12 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1342 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) (M.op X0 X2)) (M.op (M.op X1 X0) (M.op X0 X2))) = X0 ∨ (M.op (M.op X1 X0) (M.op X0 X2)) = X0 ∨ (M.op (M.op X1 X0) (M.op X0 X2)) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X2 X1) (M.op X1 X0))
       have i₂ := eq129 X0 X1 X2
       grind)
    | exact superpose eq129 eq14
    | (have j1 := eq129 X2 X0 X1
       grind)
    | exact resolve eq14 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1351 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) (M.op X0 X2)) (M.op (M.op X1 X0) (M.op X0 X2))) = X0 ∨ (M.op (M.op X1 X0) (M.op X0 X2)) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1342 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1358 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) (M.op X0 X2)) (M.op (M.op X1 X0) (M.op X0 X2))) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1341 X0 X1 X2
       have j1 := eq1351 X0 X1 X2
       grind)
    | (have r₁ := eq1341 X0 X1 X2
       have r₂ := eq1351 X0 X1 X2
       grind)
    | exact resolve eq1341 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341 eq1351
  have eq1360 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) = (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) ∨ (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1338 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq1338
    | (have j0 := eq1338 X0 X1 X2
       grind)
    | exact resolve eq1338 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq1389 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) = (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) ∨ (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1360 X0 X1 X2
       have j1 := eq85 X2 X0 X1
       grind)
    | (have r₁ := eq1360 X0 X1 X1
       have r₂ := eq85 X0 X1 X2
       grind)
    | (have r₁ := eq1360 X1 X1 X0
       have r₂ := eq85 X0 X1 X2
       grind)
    | (have r₁ := eq1360 X0 X1 X2
       have r₂ := eq85 (k (M.op (M.op X1 X0) (M.op X0 X2)) X0) (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) X2
       grind)
    | exact resolve eq1360 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1360
  have eq1673 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq115 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1674 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1673 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq1738 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq767 eq43
    | exact resolve eq43 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq1780 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq1738 eq15
    | exact resolve eq15 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq1781 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq1780
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq1780
    | exact resolve eq1780 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq1783 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq1781
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq1781
    | exact resolve eq1781 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq1784 : (M.op x y) = (M.op (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq1783
    | exact resolve eq1783 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq1818 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1784 eq12
    | (have r₁ := eq12 (τ (σ y)) (M.op x y)
       have r₂ := eq1784
       grind)
    | exact resolve eq12 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1784
  have eq1831 : (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq1818
  have eq1846 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1831 eq15
    | exact resolve eq15 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq1848 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq1846
    | exact resolve eq1846 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq1849 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1848
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq1848
    | exact resolve eq1848 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq2036 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op X1 (σ y))) ∨ (M.op X0 X0) = (M.op X1 (σ y)) ∨ (M.op X1 (σ y)) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq480 X0 x
       have i₂ := eq14 X0 (M.op x sF5)
       grind)
    | exact superpose eq14 eq480
    | (have j1 := eq14 X0 (M.op X1 (σ y))
       grind)
    | exact resolve eq480 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2056 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op X1 (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq480 eq12
    | (have r₁ := eq12 (σ y) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq480 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2105 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op X1 (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op X1 (σ y))) ∨ (M.op X0 X0) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq480 eq2036
    | (have j0 := eq2036 X0 X1
       grind)
    | exact resolve eq2036 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq2121 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op X1 (σ y))) ∨ (M.op X0 X0) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq2105 X0 X1
       have j1 := eq2056 X0 X1
       grind)
    | (have r₁ := eq2105 X0 X1
       have r₂ := eq2056 X0 X1
       grind)
    | (have r₁ := eq2105 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq2056 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq2105 (M.op (σ x) (σ y)) X1
       have r₂ := eq2056 (M.op (σ x) (σ y)) X1
       grind)
    | exact resolve eq2105 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056 eq2105
  have eq2223 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq232 eq66
    | exact resolve eq66 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2353 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op (M.op X1 X0) (M.op X0 X0))) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (M.op (M.op X1 X0) (M.op X0 X0))
       have i₂ := eq372 X1 X0
       grind)
    | exact superpose eq372 eq148
    | exact resolve eq148 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2461 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq449 X1 X2 (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0))
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq449
    | exact resolve eq449 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2466 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq449 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0))
       have i₂ := eq449 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq449 eq449
    | exact resolve eq449 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2667 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (M.op X0 X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq129 (M.op x X2) x X0
       have i₂ := eq455 X0 x X2
       grind)
    | exact superpose eq455 eq129
    | exact resolve eq129 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq2682 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op (M.op X2 (M.op X2 X0)) X3)) = (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 X3 (M.op X2 (M.op X2 X0)) (M.op x X2) X1
       have i₂ := eq455 x X2 X0
       grind)
    | exact superpose eq455 eq67
    | exact resolve eq67 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2683 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X2 X3)) (M.op X3 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq67 (M.op X3 (M.op X3 X0)) (M.op X2 X3) X4 X1
       have i₂ := eq455 X2 X3 X0
       grind)
    | exact superpose eq455 eq67
    | exact resolve eq67 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2695 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op X3 (M.op X3 (M.op X3 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2683 X0 X1 X2 X3 x
       have i₂ := eq2466 (M.op X3 (M.op X3 X0)) X3 X2 x
       grind)
    | exact superpose eq2466 eq2683
    | exact resolve eq2683 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2696 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2682 X0 x X2 X3
       have i₂ := eq2461 X3 (M.op X2 X0) X2 x
       grind)
    | exact superpose eq2461 eq2682
    | exact resolve eq2682 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461 eq2682
  have eq2737 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 X3))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2696 X0 X2 X3
       have i₂ := eq2695 (M.op X0 X3) X2 X2 X0
       grind)
    | exact superpose eq2695 eq2696
    | exact resolve eq2696 eq2695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2696
  have eq2826 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (k (τ (M.op (M.op (M.op x y) (M.op (τ (σ y)) X0)) (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)))) (τ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq220 eq2353
    | exact resolve eq2353 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2900 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (k (τ (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0))))))) (τ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq2826 x
       have i₂ := eq2695 (M.op (M.op sF2 x) (M.op sF2 x)) sF2 (τ sF5) x
       grind)
    | exact superpose eq2695 eq2826
    | exact resolve eq2826 eq2695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq2921 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (k (τ (M.op X0 (M.op X0 (M.op (M.op x y) X0)))) (τ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq2900 X0
       have i₂ := eq449 X0 sF2 (M.op sF2 X0)
       grind)
    | exact superpose eq449 eq2900
    | exact resolve eq2900 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2900
  have eq3708 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (M.op (M.op X0 (σ x)) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq279 eq372
    | exact resolve eq372 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq372
  have eq3760 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3708 x
       have i₂ := eq2695 (M.op sF6 sF6) sF4 (M.op x sF4) sF5
       grind)
    | exact superpose eq2695 eq3708
    | exact resolve eq3708 eq2695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3708
  have eq3790 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2223 eq3760
    | exact resolve eq3760 eq2223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3760
  have eq5323 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X4 (M.op (M.op X5 (M.op X6 X0)) (M.op X0 (M.op (M.op X1 X0) X2)))) X3) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq713 X3 X4 X5 (M.op X6 X0) (M.op X0 X2)
       have i₂ := eq67 X2 X0 X1 X6
       grind)
    | exact superpose eq67 eq713
    | exact resolve eq713 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq5344 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X1) = (M.op (M.op X2 (M.op (M.op X3 (σ x)) (σ y))) X1) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq70 eq713
    | exact resolve eq713 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq713
  have eq5577 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X1) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5344 X0 X0 X1 x
       have i₂ := eq2695 X0 X1 (M.op x sF4) sF5
       grind)
    | exact superpose eq2695 eq5344
    | (have j1 := eq2695 X1 (M.op X0 (σ x)) (σ x) (σ y)
       grind)
    | exact resolve eq5344 eq2695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5344
  have eq5598 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5323 X0 X1 X2 X3 x x x
       have i₂ := eq2695 X3 x (M.op x (M.op x X0)) (M.op X0 (M.op (M.op X1 X0) X2))
       grind)
    | exact superpose eq2695 eq5323
    | exact resolve eq5323 eq2695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5323
  have eq5737 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5598 X0 X1 X2 X3
       have i₂ := eq2737 (M.op (M.op X1 X0) X2) X0 (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3))
       grind)
    | exact superpose eq2737 eq5598
    | exact resolve eq5598 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5598
  have eq5849 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X2 (M.op X2 (M.op X2 (M.op X2 (M.op X2 (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5737 X0 X1 X2 X3
       have i₂ := eq2737 X2 (M.op X1 X0) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)))))
       grind)
    | exact superpose eq2737 eq5737
    | exact resolve eq5737 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737 eq5737
  have eq5941 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X2 (M.op X2 (M.op X2 (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5849 X0 X1 X2 X3
       have i₂ := eq449 X2 (M.op X1 X0) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3))))
       grind)
    | exact superpose eq449 eq5849
    | exact resolve eq5849 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5849
  have eq5978 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X2 (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5941 X0 X1 X2 X3
       have i₂ := eq449 X2 (M.op X1 X0) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)))
       grind)
    | exact superpose eq449 eq5941
    | exact resolve eq5941 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5941
  have eq6011 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X2 (M.op X2 (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5978 X0 X1 X2 X3
       have i₂ := eq2466 (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3) X2 (M.op X1 X0) X0
       grind)
    | exact superpose eq2466 eq5978
    | exact resolve eq5978 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466 eq5978
  have eq6041 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X2 (M.op X2 (M.op X2 (M.op X2 (M.op X2 (M.op X2 (M.op X2 X3))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6011 X0 x X2 X3
       have i₂ := eq2695 X3 X0 (M.op x X0) X2
       grind)
    | exact superpose eq2695 eq6011
    | exact resolve eq6011 eq2695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2695 eq6011
  have eq18558 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 (M.op sF6 (M.op sF6 x))
       have i₂ := eq455 (M.op X0 sF4) sF6 x
       grind)
    | exact superpose eq455 eq280
    | exact resolve eq280 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq18641 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))))) := by
    intro X0
    first
    | exact superpose eq5577 eq18558
    | exact resolve eq18558 eq5577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5577 eq18558
  have eq28896 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq480 eq457
    | (have j0 := eq457 (σ x) (σ y) X0 X2 X1
       grind)
    | exact resolve eq457 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28985 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) ≠ (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X0 X3)))) ∨ (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X0 X3)))) = (k X3 (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X2 (M.op X4 X1)
       have i₂ := eq457 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq457 eq12
    | exact resolve eq12 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq29247 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) ≠ (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X2 X0) (M.op X0 X3)))))))))) ∨ (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X0 X3)))) = (k X3 (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq28985 X0 X1 X2 X3 X4
       have i₂ := eq6041 X1 X0 (M.op (M.op X2 X0) (M.op X0 X3))
       grind)
    | exact superpose eq6041 eq28985
    | (have j0 := eq28985 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq28985 eq6041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28985
  have eq29329 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)))) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq240 eq28896
    | exact resolve eq28896 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28896
  have eq29763 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) ≠ (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 X3))))))) ∨ (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X0 X3)))) = (k X3 (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq29247 X0 X1 X2 X3 X4
       have i₂ := eq449 X0 X2 (M.op X0 X3)
       grind)
    | exact superpose eq449 eq29247
    | (have j0 := eq29247 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq29247 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29247
  have eq29830 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq480 eq29329
    | (have j0 := eq29329 X0 (σ x)
       grind)
    | exact resolve eq29329 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29329
  have eq30256 : ∀ X0 X2 X3 X4 : G, (k X3 (M.op X4 X0)) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X2 X0) (M.op X0 X3)))))))))) ∨ (M.op X4 X0) ≠ (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 X3))))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq29763 X0 x X2 X3 X4
       have i₂ := eq6041 x X0 (M.op (M.op X2 X0) (M.op X0 X3))
       grind)
    | exact superpose eq6041 eq29763
    | (have j0 := eq29763 X0 x X2 X3 X4
       grind)
    | (have r₁ := eq29763 X2 x X2 X2 (M.op X0 X2)
       have r₂ := eq6041 X0 X2 X2
       grind)
    | exact resolve eq29763 eq6041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29763
  have eq30311 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq232 eq29830
    | exact resolve eq29830 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq29830
  have eq30708 : ∀ X0 X3 X4 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 X3))))))) = (k X3 (M.op X4 X0)) ∨ (M.op X4 X0) ≠ (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 X3))))))) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq30256 X0 x X3 X4
       have i₂ := eq449 X0 x (M.op X0 X3)
       grind)
    | exact superpose eq449 eq30256
    | (have j0 := eq30256 X0 x X3 X4
       grind)
    | exact resolve eq30256 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30256
  have eq30753 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))))))) := by
    intro X0
    first
    | exact superpose eq18641 eq30311
    | exact resolve eq30311 eq18641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18641 eq30311
  have eq83383 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (M.op X0 X0) (M.op X0 X0)) X0 X1
       have i₂ := eq1674 X0
       grind)
    | exact superpose eq1674 eq9
    | (have j1 := eq1674 X0
       grind)
    | exact resolve eq9 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq83535 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))))))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83383 X0 x
       have i₂ := eq6041 x X0 X0
       grind)
    | exact superpose eq6041 eq83383
    | (have j0 := eq83383 X0 x
       grind)
    | exact resolve eq83383 eq6041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83383
  have eq83622 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))))))) ∨ (k (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq83535 X0
       have i₂ := eq6041 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq6041 eq83535
    | (have j0 := eq83535 X0
       grind)
    | exact resolve eq83535 eq6041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83535
  have eq83690 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))))))) := by
    intro X0
    first
    | (have j0 := eq83622 X0
       have j1 := eq30708 X0 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq83622 X0
       have r₂ := eq30708 X0 (M.op X0 X0) X0
       grind)
    | exact resolve eq83622 eq30708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30708 eq83622
  have eq388569 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (k X0 X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1358 x X0 (M.op x X2)
       have i₂ := eq455 X0 x X2
       grind)
    | exact superpose eq455 eq1358
    | exact resolve eq1358 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq421885 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq1389 x X0 (M.op x X2)
       have i₂ := eq455 X0 x X2
       grind)
    | exact superpose eq455 eq1389
    | exact resolve eq1389 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq568869 : (τ (M.op (M.op x y) (τ (σ y)))) = (k (τ (M.op (τ (σ y)) (M.op (M.op x y) (M.op (τ (σ y)) (τ (σ y)))))) (τ (M.op (M.op x y) (τ (σ y))))) := by
    first
    | exact superpose eq220 eq2921
    | exact resolve eq2921 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq2921
  have eq568918 : (τ (M.op (M.op x y) (τ (σ y)))) = (k (τ (τ (σ y))) (τ (M.op (M.op x y) (τ (σ y))))) := by
    first
    | exact superpose eq64 eq568869
    | exact resolve eq568869 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq568869
  have eq568943 : (σ (τ (M.op (M.op x y) (τ (σ y))))) = (k (σ (τ (τ (σ y)))) (σ (τ (M.op (M.op x y) (τ (σ y)))))) := by
    first
    | exact superpose eq568918 eq15
    | exact resolve eq15 eq568918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568918
  have eq568945 : (M.op (M.op x y) (τ (σ y))) = (k (σ (τ (τ (σ y)))) (M.op (M.op x y) (τ (σ y)))) := by
    first
    | (have i₁ := eq568943
       have i₂ := eq36 (M.op sF2 (τ sF5))
       grind)
    | exact superpose eq36 eq568943
    | exact resolve eq568943 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568943
  have eq568947 : (M.op (M.op x y) (τ (σ y))) = (k (τ (σ y)) (M.op (M.op x y) (τ (σ y)))) := by
    first
    | (have i₁ := eq568945
       have i₂ := eq36 (τ sF5)
       grind)
    | exact superpose eq36 eq568945
    | exact resolve eq568945 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568945
  have eq569476 : (σ (M.op (M.op x y) (τ (σ y)))) = (k (σ (τ (σ y))) (σ (M.op (M.op x y) (τ (σ y))))) := by
    first
    | exact superpose eq568947 eq15
    | exact resolve eq15 eq568947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568947
  have eq569481 : (σ (M.op (M.op x y) (τ (σ y)))) = (k (σ y) (σ (M.op (M.op x y) (τ (σ y))))) := by
    first
    | (have i₁ := eq569476
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq569476
    | exact resolve eq569476 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569476
  have eq777434 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1150 eq2223
    | exact resolve eq2223 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq2223
  have eq777492 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq777434
       have r₂ := eq366
       grind)
    | exact resolve eq777434 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777434
  have eq777621 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq777492 eq12
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq777492
       grind)
    | exact resolve eq12 eq777492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777679 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq777492
  have eq777680 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq777621
  have eq777816 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq777680 eq1109
    | exact resolve eq1109 eq777680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq777680
  have eq777978 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq777816
       have r₂ := eq777679
       grind)
    | exact resolve eq777816 eq777679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777679 eq777816
  have eq777982 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq777978
       have r₂ := eq366
       grind)
    | exact resolve eq777978 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq777978
  have eq778078 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq777982 eq240
    | exact resolve eq240 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq778079 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq777982 eq233
    | exact resolve eq233 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq778080 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq777982 eq480
    | exact resolve eq480 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq778081 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq778100 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq777982 eq9
    | exact resolve eq9 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778102 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq777982 eq12
    | exact resolve eq12 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778103 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq777982 eq14
    | exact resolve eq14 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778148 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq777982 eq449
    | exact resolve eq449 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778214 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq778103
  have eq778304 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq778102
       have r₂ := eq778214
       grind)
    | exact resolve eq778102 eq778214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778102 eq778214
  have eq778321 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33 eq778081
    | exact resolve eq778081 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778081
  have eq778322 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) X0)))))))) := by
    intro X0
    first
    | exact superpose eq30753 eq778079
    | exact resolve eq778079 eq30753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778079
  have eq778323 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) X0)))))))) := by
    intro X0
    first
    | exact superpose eq30753 eq778078
    | exact resolve eq778078 eq30753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778078
  have eq778393 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq778322 eq778323
    | exact resolve eq778323 eq778322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778322 eq778323
  have eq778587 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq778304 eq148
    | exact resolve eq148 eq778304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq778304
  have eq778765 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq778080 eq12
    | (have r₁ := eq12 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq778080 (σ y)
       grind)
    | exact resolve eq12 eq778080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780405 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq33 eq778148
    | (have j0 := eq778148 (σ y)
       grind)
    | exact resolve eq778148 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778148
  have eq780710 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq780405 eq3790
    | exact resolve eq3790 eq780405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790
  have eq780737 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq780405 eq66
    | exact resolve eq66 eq780405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq780763 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq780405 eq778100
    | exact resolve eq778100 eq780405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778100
  have eq780885 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq778393 eq780763
    | (have j1 := eq778393 (σ y)
       grind)
    | exact resolve eq780763 eq778393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778393 eq780763
  have eq780901 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y))))))))) := by
    first
    | exact superpose eq30753 eq780737
    | exact resolve eq780737 eq30753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30753 eq780737
  have eq780936 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq777982 eq780885
    | exact resolve eq780885 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780885
  have eq780945 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq780901
       have i₂ := eq83690 sF5
       grind)
    | exact superpose eq83690 eq780901
    | exact resolve eq780901 eq83690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780901
  have eq780966 : (k (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq777982 eq780945
    | exact resolve eq780945 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780945
  have eq781720 : (σ y) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | exact superpose eq780966 eq780405
    | exact resolve eq780405 eq780966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780405
  have eq781722 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq780966 eq780936
    | exact resolve eq780936 eq780966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780936 eq780966
  have eq782047 : ∀ X0 : G, (M.op (k (σ x) (σ x)) (M.op (k (σ x) (σ x)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq781720 eq449
    | exact resolve eq449 eq781720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782387 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (k (σ x) (σ x)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq781722 eq449
    | exact resolve eq449 eq781722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq782394 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (k (σ x) (σ x)))) := by
    intro X0
    first
    | exact superpose eq781722 eq455
    | exact resolve eq455 eq781722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782434 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (k (σ x) (σ x)))))))))) := by
    first
    | (have i₁ := eq782394 x
       have i₂ := eq6041 x sF4 (M.op sF4 (k sF4 sF4))
       grind)
    | exact superpose eq6041 eq782394
    | exact resolve eq782394 eq6041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782394
  have eq783803 : ∀ X0 : G, (M.op (k (σ y) (σ x)) (M.op (σ x) (M.op (σ x) X0))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq778321 eq455
    | exact resolve eq455 eq778321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778321
  have eq784848 : ∀ X0 X1 : G, (M.op (M.op X1 (σ x)) X0) = (M.op (k (σ x) (σ x)) X0) := by
    intro X0 X1
    first
    | exact superpose eq782387 eq455
    | exact resolve eq455 eq782387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784883 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) X0))))))) = (M.op (k (σ x) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq784848 x X0
       have i₂ := eq6041 X0 sF4 x
       grind)
    | exact superpose eq6041 eq784848
    | exact resolve eq784848 eq6041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784848
  have eq786579 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (M.op (σ x) (σ y))) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq781722 eq778765
    | exact resolve eq778765 eq781722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778765
  have eq788990 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (M.op (k (σ x) (σ x)) (σ y))) := by
    first
    | exact superpose eq781720 eq782047
    | exact resolve eq782047 eq781720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781720 eq782047
  have eq789115 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (k (σ x) (σ x)) (σ y))))))))) := by
    first
    | exact superpose eq784883 eq788990
    | exact resolve eq788990 eq784883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784883 eq788990
  have eq789311 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq782387 eq789115
    | exact resolve eq789115 eq782387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782387 eq789115
  have eq789326 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq33 eq789311
    | exact resolve eq789311 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789311
  have eq791311 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op (M.op X0 (σ x)) (M.op (σ x) (k (σ x) (σ x)))) := by
    intro X0
    first
    | exact superpose eq789326 eq455
    | exact resolve eq455 eq789326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789326
  have eq791318 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (k (σ x) (σ x)))))))))) := by
    first
    | (have i₁ := eq791311 x
       have i₂ := eq6041 x sF4 (M.op sF4 (k sF4 sF4))
       grind)
    | exact superpose eq6041 eq791311
    | exact resolve eq791311 eq6041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791311
  have eq791349 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq782434 eq791318
    | exact resolve eq791318 eq782434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782434 eq791318
  have eq792871 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq791349 eq455
    | exact resolve eq455 eq791349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq792899 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x))))))))) := by
    first
    | (have i₁ := eq792871 x
       have i₂ := eq6041 x sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq6041 eq792871
    | exact resolve eq792871 eq6041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6041 eq792871
  have eq792942 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq792899
       have i₂ := eq83690 sF4
       grind)
    | exact superpose eq83690 eq792899
    | exact resolve eq792899 eq83690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83690 eq792899
  have eq792956 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq781722 eq792942
    | exact resolve eq792942 eq781722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792942
  have eq793803 : (σ x) = (M.op (σ x) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) := by
    first
    | exact superpose eq792956 eq791349
    | exact resolve eq791349 eq792956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791349
  have eq799953 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ x)) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq792956 eq783803
    | exact resolve eq783803 eq792956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783803 eq792956
  have eq856125 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq778080 X0
       have i₂ := eq2667 X0 sF6
       grind)
    | exact superpose eq2667 eq778080
    | (have j1 := eq2667 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq778080 eq2667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq857277 : (k (σ x) (M.op (σ x) (σ y))) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq781722 eq856125
    | exact resolve eq856125 eq781722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781722 eq856125
  have eq857949 : (k (σ x) (M.op (σ x) (σ y))) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq857277
       have r₂ := eq786579
       grind)
    | exact resolve eq857277 eq786579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786579 eq857277
  have eq858263 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (k (τ (σ y)) X0) X1) ∨ (k (τ (σ y)) (τ (σ y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq468 X1 x
       have i₂ := eq388569 (τ sF5) x
       grind)
    | exact superpose eq388569 eq468
    | (have j1 := eq388569 (τ (σ y)) X0
       grind)
    | exact resolve eq468 eq388569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq388569
  have eq859742 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (k (τ (σ y)) X0) X1) ∨ (τ (σ x)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq778587 eq858263
    | (have j0 := eq858263 X0 X1
       grind)
    | exact resolve eq858263 eq778587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858263
  have eq868995 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (τ (σ x)) X0) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq778587 eq859742
    | (have j0 := eq859742 (τ (σ y)) x
       grind)
    | exact resolve eq859742 eq778587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778587 eq859742
  have eq869154 : (M.op x y) = (M.op (M.op x y) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq868995 eq43
    | exact resolve eq43 eq868995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868995
  have eq871076 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq869154 eq569481
    | exact resolve eq569481 eq869154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569481 eq869154
  have eq871154 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq27 eq871076
    | exact resolve eq871076 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871076
  have eq871181 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq871154 eq120
    | (have j0 := eq120 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq120 (σ (M.op x y)) (σ y)
       have r₂ := eq871154
       grind)
    | exact resolve eq120 eq871154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq871184 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq871181
  have eq871187 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq777982 eq871184
    | exact resolve eq871184 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871184
  have eq981279 : ∀ X0 X1 : G, (k X0 (M.op X1 (σ y))) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq778080 sF6
       have i₂ := eq2121 sF6 X1
       grind)
    | (have i₁ := eq778080 (σ y)
       have i₂ := eq2121 X0 sF6
       grind)
    | exact superpose eq2121 eq778080
    | (have j1 := eq2121 X0 X1
       grind)
    | exact resolve eq778080 eq2121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121 eq778080
  have eq983373 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 (σ y))) ∨ (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq981279 eq33
    | (have j1 := eq981279 (σ y) X0
       grind)
    | exact resolve eq33 eq981279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq981279
  have eq983507 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 (σ y))) ∨ (σ x) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq777982 eq983373
    | (have j0 := eq983373 X0
       grind)
    | exact resolve eq983373 eq777982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777982 eq983373
  have eq984584 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq871187 eq983507
    | exact resolve eq983507 eq871187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871187 eq983507
  have eq984611 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq984584
  have eq986315 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq984611 eq34
    | exact resolve eq34 eq984611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984611
  have eq986376 : (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq986315
       have r₂ := eq871154
       grind)
    | exact resolve eq986315 eq871154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871154 eq986315
  have eq986377 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq986376 eq43
    | exact resolve eq43 eq986376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq986521 : (σ y) = (σ (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq986376 eq36
    | exact resolve eq36 eq986376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986376
  have eq986535 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq986521
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq986521
    | exact resolve eq986521 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986521
  have eq993066 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq986535 eq780710
    | exact resolve eq780710 eq986535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780710 eq986535
  have eq993293 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq857949 eq993066
    | exact resolve eq993066 eq857949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857949 eq993066
  have eq996982 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq993293 eq34
    | exact resolve eq34 eq993293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993293
  have eq1007297 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq986377 eq421885
    | exact resolve eq421885 eq986377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421885 eq986377
  have eq1007301 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1007297
  have eq1009207 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1007301 eq15
    | exact resolve eq15 eq1007301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007301
  have eq1009210 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1009207
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq1009207
    | exact resolve eq1009207 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1009207
  have eq1009211 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq1009210
    | exact resolve eq1009210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1009210
  have eq1009212 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1009211
       have r₂ := eq996982
       grind)
    | exact resolve eq1009211 eq996982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996982 eq1009211
  have eq1010032 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1009212 eq1849
    | exact resolve eq1849 eq1009212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849
  have eq1010092 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1010032
  have eq1011536 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1010092 eq799953
    | exact resolve eq799953 eq1010092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799953 eq1010092
  have eq1011607 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq793803 eq1011536
    | exact resolve eq1011536 eq793803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793803 eq1011536
  have eq1011608 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1011607
  have eq1014479 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1011608 eq34
    | exact resolve eq34 eq1011608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1011608
  have eq1015539 : False := by grind
  exact eq1015539

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : x ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq66 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  clear eq36
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq93 : ∀ X0 : G, (σ (k (k y x) X0)) = (k (k (σ y) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k y x) X0
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq10
    | exact resolve eq10 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq111 (σ X0)
       grind)
    | exact superpose eq111 eq10
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq75
    | exact resolve eq75 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq118 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq115
    | exact resolve eq115 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq113
    | exact resolve eq113 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq127 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq103
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq103
    | exact resolve eq103 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq127
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq127
    | exact resolve eq127 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq253 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq14
    | exact resolve eq14 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X4 (M.op (M.op X2 X1) (M.op X1 X0))) X3)) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op (M.op X2 X1) (M.op X1 X0)) X4 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X1) X2) (M.op (M.op X5 (M.op (M.op X3 X1) X2)) X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op (M.op X3 X1) X2) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 (M.op (M.op X3 X1) X2) X5 X1
       have i₂ := eq55 X2 X1 X3 X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X2) (M.op (M.op X5 (M.op X0 X2)) X4)) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op (M.op X0 X2) X4)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq55 X4 (M.op X0 X2) X5 (M.op x X0)
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X3 X2) (M.op X2 X0)))) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X3 X2) (M.op X2 X0)) X2 X4 X1
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X0) (M.op (M.op X5 (M.op X4 X0)) (M.op X0 X2))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X0 X2) (M.op X4 X0) X5 X3
       have i₂ := eq55 X2 X0 X1 X4
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op (M.op X0 X2) X4)) = (M.op (M.op X0 X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X4 (M.op X0 X2) (M.op x X0) X3
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X2 (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X4 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X4 X2) X0)) X2 X4 X1
       have i₂ := eq14 X0 (M.op X4 X2) X3
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq559 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 x
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X3 X0)) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X2) (M.op X3 X0) X4
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op (M.op X5 (M.op (M.op X2 X3) (M.op X3 X4))) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) (M.op (M.op X2 X3) (M.op X3 X4)) X5 X1
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq253 eq50
    | exact resolve eq50 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1056 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op X2 y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1038 eq55
    | exact resolve eq55 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1058 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1056 X0 X1 x
       have i₂ := eq14 (M.op sF0 X0) y x
       grind)
    | exact superpose eq14 eq1056
    | exact resolve eq1056 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1097 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq258 eq51
    | exact resolve eq51 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1115 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1097 eq55
    | exact resolve eq55 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1115 X0 X1 x
       have i₂ := eq14 (M.op sF4 X0) sF3 x
       grind)
    | exact superpose eq14 eq1115
    | exact resolve eq1115 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1164 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq555 X1 (σ X0) (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq555
    | exact resolve eq555 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1179 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq555 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq55 X2 X1 X4 X0
       grind)
    | exact superpose eq55 eq555
    | exact resolve eq555 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq555 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq555 X0 X2 X3
       grind)
    | exact superpose eq555 eq555
    | exact resolve eq555 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq555 (σ X0) X1 (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq555
    | exact resolve eq555 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1238 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1179 x X1 X2 X4 X3
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq1179
    | exact resolve eq1179 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1406 : ∀ X1 X2 : G, (M.op y X1) = (M.op (M.op X2 (M.op x (M.op x y))) X1) := by
    intro X1 X2
    first
    | exact superpose eq557 eq1238
    | exact resolve eq1238 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1407 : ∀ X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X2 (M.op (σ x) (M.op (σ x) (σ y)))) X1) := by
    intro X1 X2
    first
    | exact superpose eq558 eq1238
    | exact resolve eq1238 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq4619 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op X0 (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq258 eq262
    | exact resolve eq262 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq4682 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 (M.op sF4 (M.op sF4 X0))
       have i₂ := eq555 X0 (M.op X0 sF2) sF4
       grind)
    | exact superpose eq555 eq268
    | exact resolve eq268 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq7541 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op x y) (M.op y (M.op (M.op X1 (M.op X2 y)) (M.op (M.op X2 y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq553 X0 x y X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq553
    | (have j0 := eq553 X0 x y X1 X2
       grind)
    | exact resolve eq553 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq7804 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X2 y)) (M.op (M.op X2 y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq253 eq7541
    | exact resolve eq7541 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7541
  have eq7830 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X2 y)) (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7804 X0 X1 X2
       have i₂ := eq1058 X0 X2
       grind)
    | (have i₁ := eq7804 X0 X1 x
       have i₂ := eq1058 X0 X1
       grind)
    | exact superpose eq1058 eq7804
    | exact resolve eq7804 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7804
  have eq7943 : ∀ X0 X2 X3 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op X3 (M.op (σ x) (M.op (σ x) (σ y)))) X0)))) := by
    intro X0 X2 X3
    first
    | exact superpose eq558 eq564
    | exact resolve eq564 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq7987 : ∀ X0 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op x (M.op x y)) (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op x y)) X0)))) := by
    intro X0 X2
    first
    | exact superpose eq557 eq564
    | exact resolve eq564 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8243 : ∀ X0 X3 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op X3 (M.op (σ x) (M.op (σ x) (σ y)))) X0)))) := by
    intro X0 X3
    first
    | exact superpose eq1117 eq7943
    | (have j0 := eq7943 X0 (σ x) X3
       grind)
    | exact resolve eq7943 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq8253 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq1407 eq8243
    | exact resolve eq8243 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407 eq8243
  have eq11468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11468
    | exact resolve eq11468 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11468
  have eq11480 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11469
       have r₂ := eq27
       grind)
    | exact resolve eq11469 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11469
  have eq11484 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11480
    | exact resolve eq11480 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11480
  have eq11486 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11484
    | exact resolve eq11484 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11484
  have eq11499 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11486 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11486
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11486
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11486
       grind)
    | exact resolve eq12 eq11486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11486
  have eq11544 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11499
       have r₂ := eq26
       grind)
    | exact resolve eq11499 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11499
  have eq11551 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11544
    | exact resolve eq11544 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11544
  have eq11552 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq11551
  have eq11776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11552 eq98
    | exact resolve eq98 eq11552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq11552
  have eq11784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11776
  have eq11786 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11784
       have r₂ := eq27
       grind)
    | exact resolve eq11784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11784
  have eq11799 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11786
       grind)
    | exact superpose eq11786 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11786
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11786
       grind)
    | exact resolve eq12 eq11786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11786
  have eq11844 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11799
       have r₂ := eq18
       grind)
    | exact resolve eq11799 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11799
  have eq11851 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11844
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11844
    | exact resolve eq11844 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11844
  have eq11852 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11851
  have eq11858 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11852
       grind)
    | exact superpose eq11852 eq74
    | exact resolve eq74 eq11852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11852
  have eq11872 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11858
    | exact resolve eq11858 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11858
  have eq11887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11872 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11887
    | exact resolve eq11887 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11887
  have eq11901 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11890
       have r₂ := eq27
       grind)
    | exact resolve eq11890 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11890
  have eq11905 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11901
    | exact resolve eq11901 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11901
  have eq11907 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11905
    | exact resolve eq11905 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11905
  have eq11908 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11907
  have eq11922 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11908 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11908
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11908
       grind)
    | exact resolve eq12 eq11908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11908
  have eq11967 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11922
       have r₂ := eq26
       grind)
    | exact resolve eq11922 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11922
  have eq11974 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11967
    | exact resolve eq11967 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11967
  have eq11975 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11974
  have eq11993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11975 eq11872
    | exact resolve eq11872 eq11975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11872 eq11975
  have eq11995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11993
  have eq11999 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11995
       have r₂ := eq27
       grind)
    | exact resolve eq11995 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11995
  have eq12174 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11999 eq66
    | (have r₁ := eq66
       have r₂ := eq11999
       grind)
    | exact resolve eq66 eq11999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq12180 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11999 eq1097
    | exact resolve eq1097 eq11999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq12184 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12174
  have eq12192 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12184 eq94
    | exact resolve eq94 eq12184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq12184
  have eq12219 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq12192
    | exact resolve eq12192 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq12192
  have eq12222 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq12219
       have r₂ := eq65
       grind)
    | exact resolve eq12219 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq12219
  have eq12228 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq12222
       grind)
    | exact superpose eq12222 eq74
    | exact resolve eq74 eq12222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq12244 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12228
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq12228
    | exact resolve eq12228 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12228
  have eq12256 : ∀ X0 : G, (σ (k (k y x) X0)) = (k (M.op (σ y) (σ y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq12244 eq93
    | exact resolve eq93 eq12244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq12244
  have eq12277 : ∀ X0 : G, (σ (k (M.op y y) X0)) = (k (M.op (σ y) (σ y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12256 X0
       have i₂ := eq12222
       grind)
    | exact superpose eq12222 eq12256
    | exact resolve eq12256 eq12222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12222 eq12256
  have eq12629 : ∀ X0 X1 : G, (M.op y (M.op (M.op x (M.op x y)) X1)) = (M.op (M.op x (M.op x y)) (M.op (M.op X0 (M.op x (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq529
    | exact resolve eq529 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq529
  have eq12914 : ∀ X1 : G, (M.op y (M.op (M.op x (M.op x y)) X1)) = (M.op (M.op x (M.op x y)) (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq1406 eq12629
    | exact resolve eq12629 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12629
  have eq13492 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12180
    | (have j0 := eq12180 (σ y)
       grind)
    | exact resolve eq12180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12180
  have eq13752 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11999 eq13492
    | exact resolve eq13492 eq11999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11999 eq13492
  have eq13798 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq13752
  have eq14272 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op (M.op x (M.op x (M.op x y))) X1)) = (M.op (M.op x (M.op x (M.op x y))) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq557 eq550
    | exact resolve eq550 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq557
  have eq14549 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X1)) = (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op (M.op x (M.op x (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1406 eq14272
    | exact resolve eq14272 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14272
  have eq14612 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X1)) = (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq1406 eq14549
    | exact resolve eq14549 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406 eq14549
  have eq14638 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X1)) = (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14612 X0 X1
       have i₂ := eq1058 X1 x
       grind)
    | (have i₁ := eq14612 X0 X0
       have i₂ := eq1058 X0 X1
       grind)
    | exact superpose eq1058 eq14612
    | (have j0 := eq14612 X0 X1
       grind)
    | exact resolve eq14612 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14612
  have eq14648 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13798 eq555
    | exact resolve eq555 eq13798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13798
  have eq14708 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1117 eq14648
    | (have j0 := eq14648 (σ x)
       grind)
    | exact resolve eq14648 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14648
  have eq18626 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op y (M.op (M.op X4 y) (M.op (M.op x y) (M.op y X0))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq50 eq539
    | exact resolve eq539 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19058 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X3 X1) (M.op (M.op X4 (M.op X3 X1)) (M.op X1 (M.op (M.op X5 X1) (M.op X1 X2))))) = (M.op (M.op X6 (M.op X3 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq539 X1 x (M.op (M.op X5 X1) (M.op X1 X2)) X6 X3 X4
       have i₂ := eq537 X2 X0 X1 X5 x
       grind)
    | exact superpose eq537 eq539
    | exact resolve eq539 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq19330 : ∀ X0 X1 X2 X3 X6 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X6 (M.op X3 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq19058 X0 X1 X2 X3 x x X6
       have i₂ := eq564 X1 x (M.op X1 X2) X3 x
       grind)
    | exact superpose eq564 eq19058
    | exact resolve eq19058 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq19058
  have eq19458 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18626 X0 X1 X2 X3 x
       have i₂ := eq1058 (M.op sF0 (M.op y X0)) X1
       grind)
    | (have i₁ := eq18626 X0 X1 X2 X3 X1
       have i₂ := eq1058 (M.op sF0 (M.op y X0)) X1
       grind)
    | exact superpose eq1058 eq18626
    | (have j0 := eq18626 X0 X1 X2 X3 x
       grind)
    | exact resolve eq18626 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18626
  have eq19545 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq253 eq19458
    | exact resolve eq19458 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19458
  have eq19570 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq50 eq19545
    | exact resolve eq19545 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq19545
  have eq19572 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op (M.op X2 (M.op X1 y)) X0)) = (M.op (M.op X3 (M.op X1 y)) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19570 X0 X1 X2 X3
       have i₂ := eq1058 (M.op (M.op X2 (M.op X1 y)) X0) X1
       grind)
    | (have i₁ := eq19570 X0 x X2 X3
       have i₂ := eq1058 (M.op (M.op X2 (M.op x y)) X0) X1
       grind)
    | exact superpose eq1058 eq19570
    | exact resolve eq19570 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19570
  have eq26576 : ∀ X0 X1 X2 X3 X4 X5 X7 : G, (M.op (M.op X7 (M.op (M.op X3 X1) X2)) X5) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op (M.op X3 X1) X2) (M.op (M.op X4 (M.op (M.op X3 X1) X2)) (M.op (M.op (M.op X3 X1) X2) X5)))) := by
    intro X0 X1 X2 X3 X4 X5 X7
    first
    | (have i₁ := eq537 X5 X7 (M.op (M.op X3 X1) X2) X4 x
       have i₂ := eq528 X0 X1 X2 X3 (M.op (M.op X4 (M.op (M.op X3 X1) X2)) (M.op (M.op (M.op X3 X1) X2) X5)) x
       grind)
    | exact superpose eq528 eq537
    | exact resolve eq537 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq26781 : ∀ X0 X1 X2 X3 X5 X7 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X5) = (M.op (M.op X7 (M.op (M.op X3 X1) X2)) X5) := by
    intro X0 X1 X2 X3 X5 X7
    first
    | (have i₁ := eq26576 X0 X1 X2 X3 x X5 X7
       have i₂ := eq14 X5 (M.op (M.op X3 X1) X2) x
       grind)
    | exact superpose eq14 eq26576
    | exact resolve eq26576 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26576
  have eq35841 : (σ (k (M.op y y) (M.op y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq12277 (M.op y y)
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq12277
    | exact resolve eq12277 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12277
  have eq35949 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq35841
       have i₂ := eq111 (M.op sF3 sF3)
       grind)
    | exact superpose eq111 eq35841
    | exact resolve eq35841 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35841
  have eq35964 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq35949
       have i₂ := eq111 (M.op y y)
       grind)
    | exact superpose eq111 eq35949
    | exact resolve eq35949 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq35949
  have eq35968 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1117 eq35964
    | exact resolve eq35964 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35964
  have eq35971 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq258 eq35968
    | exact resolve eq35968 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq35968
  have eq35974 : (σ (M.op (M.op x y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq35971
       have i₂ := eq1058 (M.op y y) y
       grind)
    | exact superpose eq1058 eq35971
    | exact resolve eq35971 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35971
  have eq35977 : (σ (M.op y (M.op (M.op x y) y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq253 eq35974
    | exact resolve eq35974 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35974
  have eq43104 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq637 X0 X1 X2 X3 X4 x
       have i₂ := eq527 X4 X3 X2 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) x
       grind)
    | exact superpose eq527 eq637
    | exact resolve eq637 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq637
  have eq43105 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq43104 X0 X1 X2 X3 X4
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq43104
    | exact resolve eq43104 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq43104
  have eq43586 : ∀ X0 X1 X2 X3 X5 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X0 (M.op (M.op X5 (M.op X5 X0)) X1))) X2) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq43105 X2 X3 (M.op x X5) (M.op X5 (M.op X5 X0)) X1
       have i₂ := eq555 X0 x X5
       grind)
    | exact superpose eq555 eq43105
    | exact resolve eq43105 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq43105
  have eq85894 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) (M.op y y))) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1164 (M.op y y) x
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq1164
    | exact resolve eq1164 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq1164
  have eq86151 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) (M.op y y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1117 eq85894
    | exact resolve eq85894 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85894
  have eq86178 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) (M.op y y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1117 eq86151
    | exact resolve eq86151 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86151
  have eq86187 : ∀ X0 : G, (M.op (σ (M.op (M.op x y) (M.op y y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq86178 X0
       have i₂ := eq1058 (M.op y y) y
       grind)
    | exact superpose eq1058 eq86178
    | exact resolve eq86178 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86178
  have eq86192 : ∀ X0 : G, (M.op (σ (M.op y (M.op (M.op x y) y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq253 eq86187
    | exact resolve eq86187 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq86187
  have eq86195 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq35977 eq86192
    | exact resolve eq86192 eq35977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35977 eq86192
  have eq86278 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq86195 (M.op (M.op X1 sF4) x)
       have i₂ := eq559 sF4 X1 x
       grind)
    | exact superpose eq559 eq86195
    | exact resolve eq86195 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86195
  have eq111155 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq86278 eq4682
    | exact resolve eq4682 eq86278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682 eq86278
  have eq111216 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0
    first
    | exact superpose eq111155 eq4619
    | exact resolve eq4619 eq111155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4619
  have eq111460 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0
    first
    | exact superpose eq111155 eq111216
    | exact resolve eq111216 eq111155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111155 eq111216
  have eq111721 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq111460 (M.op (M.op X1 sF4) x)
       have i₂ := eq559 sF4 X1 x
       grind)
    | exact superpose eq559 eq111460
    | exact resolve eq111460 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112634 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ y) (M.op (M.op X1 (σ y)) (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))))) = (M.op (M.op X4 (σ y)) (M.op (M.op X3 (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq111721 eq537
    | exact resolve eq537 eq111721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111721
  have eq112747 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 (M.op (σ x) (σ y))) X0)) = (M.op (σ y) (M.op (M.op X1 (σ y)) (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1117 eq112634
    | (have j0 := eq112634 X0 X1 X2 X3 (σ x)
       grind)
    | exact resolve eq112634 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112634
  have eq112800 : ∀ X0 X2 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 (M.op (σ x) (σ y))) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq1117 eq112747
    | (have j0 := eq112747 X0 (σ x) X2 X3
       grind)
    | exact resolve eq112747 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112747
  have eq112820 : ∀ X0 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 (M.op (σ x) (σ y))) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X3
    first
    | exact superpose eq1117 eq112800
    | (have j0 := eq112800 X0 (σ x) X3
       grind)
    | exact resolve eq112800 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112800
  have eq112827 : ∀ X0 X3 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 (M.op (σ x) (σ y))) X0)) := by
    intro X0 X3
    first
    | exact superpose eq111460 eq112820
    | exact resolve eq112820 eq111460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111460 eq112820
  have eq186513 : ∀ X0 X2 : G, (M.op (M.op x y) X0) = (M.op y (M.op (M.op x (M.op x y)) (M.op (M.op x y) (M.op (M.op X2 (M.op x y)) X0)))) := by
    intro X0 X2
    first
    | exact superpose eq12914 eq7987
    | exact resolve eq7987 eq12914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7987 eq12914
  have eq196257 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq112827 eq8253
    | exact resolve eq8253 eq112827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8253 eq112827
  have eq237461 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op (M.op (σ y) (M.op (σ y) X0)) (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq196257 eq43586
    | exact resolve eq43586 eq196257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43586 eq196257
  have eq238858 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq237461 X1 X2 X2 X3
       have i₂ := eq19330 (M.op sF2 sF4) X1 X2 sF3 sF3
       grind)
    | exact superpose eq19330 eq237461
    | exact resolve eq237461 eq19330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19330 eq237461
  have eq261385 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op x (M.op x y)) (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) X0))))) = (M.op (M.op X2 (M.op x (M.op x (M.op x y)))) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq186513 eq14638
    | exact resolve eq14638 eq186513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14638 eq186513
  have eq261661 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op y (M.op (M.op x y) (M.op (M.op x (M.op x y)) (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261385 X0 X1 x
       have i₂ := eq238858 x sF0 (M.op sF0 X0) x
       grind)
    | exact superpose eq238858 eq261385
    | exact resolve eq261385 eq238858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261385
  have eq261802 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X1 (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq261661 X0 X1
       have i₂ := eq14 (M.op (M.op X1 sF0) X0) sF0 x
       grind)
    | exact superpose eq14 eq261661
    | exact resolve eq261661 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261661
  have eq262032 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op (M.op X2 (M.op X1 (M.op x y))) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq261802 (M.op (M.op X1 sF0) (M.op (M.op X1 (M.op X1 sF0)) X2)) X1
       have i₂ := eq559 (M.op X1 sF0) X1 X2
       grind)
    | exact superpose eq559 eq261802
    | exact resolve eq261802 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261802
  have eq262352 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op X2 (M.op X1 (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262032 X0 X1 X2
       have i₂ := eq559 sF0 X1 (M.op (M.op X2 (M.op X1 sF0)) X0)
       grind)
    | exact superpose eq559 eq262032
    | exact resolve eq262032 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262032
  have eq262768 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op (M.op X1 (M.op x y)) (M.op y X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq262352 eq559
    | exact resolve eq559 eq262352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq262352
  have eq264634 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op (M.op X2 (M.op X3 y)) (M.op (M.op x y) X0))) = (M.op (M.op X1 (M.op x y)) (M.op (M.op X1 (M.op x y)) (M.op y X0))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq7830 eq262768
    | exact resolve eq262768 eq7830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7830
  have eq265025 : ∀ X0 X2 X3 : G, (M.op (M.op x y) (M.op (M.op X2 (M.op X3 y)) (M.op (M.op x y) X0))) = X0 := by
    intro X0 X2 X3
    first
    | exact superpose eq262768 eq264634
    | exact resolve eq264634 eq262768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262768 eq264634
  have eq268738 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op (M.op X1 (M.op X0 y)) (M.op (M.op X2 (M.op X0 y)) (M.op (M.op X0 y) (M.op (M.op x y) X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq265025 X0 X1 X3
       have i₂ := eq537 (M.op sF0 X0) X1 (M.op X3 y) X3 x
       grind)
    | exact superpose eq537 eq265025
    | exact resolve eq265025 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq265025
  have eq268986 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op X0 y)) (M.op (M.op X2 (M.op X0 y)) (M.op (M.op X0 y) (M.op (M.op x y) X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq268738 x X1 X2 X3
       have i₂ := eq1058 (M.op (M.op X1 (M.op x y)) (M.op (M.op X2 (M.op x y)) (M.op (M.op x y) (M.op sF0 X3)))) X1
       grind)
    | (have i₁ := eq268738 X1 X1 X2 X3
       have i₂ := eq1058 (M.op (M.op X1 (M.op X1 y)) (M.op (M.op X2 (M.op X1 y)) (M.op (M.op X1 y) (M.op sF0 X3)))) X1
       grind)
    | exact superpose eq1058 eq268738
    | exact resolve eq268738 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268738
  have eq269026 : ∀ X0 X1 X3 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op X0 y)) (M.op y (M.op y (M.op (M.op x y) X3)))))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq268986 x X1 X1 X3
       have i₂ := eq1181 (M.op sF0 X3) X1 x y
       grind)
    | exact superpose eq1181 eq268986
    | exact resolve eq268986 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq268986
  have eq269036 : ∀ X0 X1 X3 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (M.op X0 y)) X3))) = X3 := by
    intro X0 X1 X3
    first
    | exact superpose eq1038 eq269026
    | exact resolve eq269026 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq269026
  have eq513252 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (σ X0)) X2) = (M.op (M.op (M.op X1 (σ X0)) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26781 X1 (σ X0) (M.op (σ X0) (σ (M.op X0 X0))) x X2 X3
       have i₂ := eq1187 X0 x
       grind)
    | exact superpose eq1187 eq26781
    | exact resolve eq26781 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq26781
  have eq516457 : ∀ X0 X2 X3 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (M.op X3 (σ X0)) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq513252 X0 x X2 X3
       have i₂ := eq238858 (σ X0) (σ (M.op X0 X0)) X2 (M.op x (σ X0))
       grind)
    | exact superpose eq238858 eq513252
    | exact resolve eq513252 eq238858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238858 eq513252
  have eq520817 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq513 X0 x
       have i₂ := eq516457 X0 (σ (M.op X0 X0)) x
       grind)
    | exact superpose eq516457 eq513
    | exact resolve eq513 eq516457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq516457
  have eq521593 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq520817 X0
       have i₂ := eq120 (M.op X0 X0)
       grind)
    | exact superpose eq120 eq520817
    | exact resolve eq520817 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq520817
  have eq522198 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq521593 X0
       have i₂ := eq55 X0 X0 X1 X0
       grind)
    | exact superpose eq55 eq521593
    | exact resolve eq521593 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq521593
  have eq535949 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op x y) y)) y))))) := by
    intro X0
    first
    | exact superpose eq19572 eq522198
    | exact resolve eq522198 eq19572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19572 eq522198
  have eq536388 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op x y) y)) y))))) := by
    intro X0
    first
    | (have i₁ := eq535949 X0
       have i₂ := eq1058 (M.op sF0 (M.op (M.op X0 (M.op sF0 y)) y)) sF0
       grind)
    | exact superpose eq1058 eq535949
    | exact resolve eq535949 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535949
  have eq536889 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ y)) := by
    first
    | (have i₁ := eq536388 x
       have i₂ := eq269036 x x (M.op sF0 (M.op sF0 (M.op (M.op x (M.op sF0 y)) y)))
       grind)
    | exact superpose eq269036 eq536388
    | exact resolve eq536388 eq269036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269036 eq536388
  have eq537132 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ y)) := by
    first
    | (have i₁ := eq536889
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq536889
    | exact resolve eq536889 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq536889
  have eq537300 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq537132 eq1117
    | exact resolve eq1117 eq537132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq542704 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq537132 eq537300
    | exact resolve eq537300 eq537132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537300
  have eq543688 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq542704 eq16
    | exact resolve eq16 eq542704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542704
  have eq549509 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14708 eq543688
    | exact resolve eq543688 eq14708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14708 eq543688
  have eq549733 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq549509
    | exact resolve eq549509 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq549509
  have eq549779 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq549733 eq1058
    | exact resolve eq1058 eq549733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq555329 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq549779 eq549733
    | exact resolve eq549733 eq549779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549733 eq549779
  have eq556176 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq555329
  have eq556299 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq556176
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq556176
    | exact resolve eq556176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556176
  have eq556300 : x = (M.op x y) := by grind
  clear eq556299
  have eq556452 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq556300 eq20
    | exact resolve eq20 eq556300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556679 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq556300 eq537132
    | exact resolve eq537132 eq556300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537132 eq556300
  have eq556687 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq556679
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq556679
    | exact resolve eq556679 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq556679
  have eq556835 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq556452
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq556452
    | exact resolve eq556452 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq556452
  have eq556839 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq556687
    | exact resolve eq556687 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq556687
  have eq556897 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq556835 eq26
    | exact resolve eq26 eq556835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq556835
  have eq558345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq556839 eq556897
    | exact resolve eq556897 eq556839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556839 eq556897
  have eq558346 : False := by grind
  exact eq558346

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq75
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq75 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq114 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq114 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq114 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq119 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq115 y
       grind)
    | exact superpose eq115 eq76
    | exact resolve eq76 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq122 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq115 sF3
       grind)
    | exact superpose eq115 eq119
    | exact resolve eq119 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq126 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq103
       have i₂ := eq115 sF3
       grind)
    | exact superpose eq115 eq103
    | exact resolve eq103 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq115 y
       grind)
    | exact superpose eq115 eq126
    | exact resolve eq126 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq126
  have eq252 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op X1 y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op X1 (σ y)) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op x sF3) (M.op sF3 X0))
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X4 (M.op (M.op X2 X1) (M.op X1 X0))) X3)) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op (M.op X2 X1) (M.op X1 X0)) X4 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op X2 y) (M.op (M.op x y) (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq55
    | exact resolve eq55 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 x
       have i₂ := eq55 X2 X0 X1 x
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op (M.op X5 (M.op (M.op X2 X3) (M.op X3 X4))) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) (M.op (M.op X2 X3) (M.op X3 X4)) X5 X1
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq98 eq69
    | (have j0 := eq69 (σ y) (σ x)
       grind)
    | exact resolve eq69 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq949
    | exact resolve eq949 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq953 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq950
       have r₂ := eq27
       grind)
    | exact resolve eq950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq955 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq953
    | exact resolve eq953 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq957 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq955 eq51
    | exact resolve eq51 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq959 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq955 eq54
    | exact resolve eq54 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq961 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq955 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq955
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq955
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq955
       grind)
    | exact resolve eq12 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq961
       have r₂ := eq26
       grind)
    | exact resolve eq961 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq971 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq969
    | exact resolve eq969 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq1008 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq955 eq257
    | exact resolve eq257 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq1118 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0))) = X0 ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq959 eq515
    | exact resolve eq515 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515 eq959
  have eq1421 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq971 eq98
    | exact resolve eq98 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq1424 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1421
  have eq1695 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X1 y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq252 eq255
    | exact resolve eq255 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1762 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq955 eq258
    | exact resolve eq258 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq2325 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1762 eq519
    | exact resolve eq519 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq2916 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1008 eq2325
    | exact resolve eq2325 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008 eq2325
  have eq2934 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq2916
  have eq6273 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq504 X0 X1 x
       have i₂ := eq1695 (M.op sF0 (M.op y X0)) X1
       grind)
    | (have i₁ := eq504 X0 X1 X1
       have i₂ := eq1695 (M.op sF0 (M.op y X0)) X1
       grind)
    | exact superpose eq1695 eq504
    | (have j0 := eq504 X0 X1 x
       grind)
    | exact resolve eq504 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq1695
  have eq6274 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1
    first
    | exact superpose eq252 eq6273
    | exact resolve eq6273 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq6273
  have eq6275 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | exact superpose eq50 eq6274
    | exact resolve eq6274 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6274
  have eq25531 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq1118 (M.op (M.op X1 (M.op sF4 sF4)) x)
       have i₂ := eq519 (M.op sF4 sF4) X1 x
       grind)
    | exact superpose eq519 eq1118
    | exact resolve eq1118 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq1118
  have eq25645 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq957 eq25531
    | exact resolve eq25531 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq25531
  have eq25898 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq25645 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25645
  have eq26159 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq25898 eq2934
    | exact resolve eq2934 eq25898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2934
  have eq26176 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq25898 eq955
    | exact resolve eq955 eq25898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq26177 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq25898 eq127
    | exact resolve eq127 eq25898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq25898
  have eq26353 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq26176
  have eq26367 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq26159
  have eq26430 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq26177
    | exact resolve eq26177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26177
  have eq26480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26353 eq1424
    | exact resolve eq1424 eq26353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424 eq26353
  have eq26581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26480
  have eq26589 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26581
       have r₂ := eq27
       grind)
    | exact resolve eq26581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26581
  have eq28579 : (M.op (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq26430
       grind)
    | exact superpose eq26430 eq122
    | exact resolve eq122 eq26430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26430
  have eq28674 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28579
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq28579
    | exact resolve eq28579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28579
  have eq28910 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28674 eq51
    | exact resolve eq51 eq28674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq28674
  have eq50821 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26367 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26367
  have eq50908 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq50821
       have r₂ := eq26589
       grind)
    | exact resolve eq50821 eq26589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26589 eq50821
  have eq63289 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28910 eq50908
    | exact resolve eq50908 eq28910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28910 eq50908
  have eq63296 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq63289
  have eq64716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq63296 eq98
    | exact resolve eq98 eq63296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq63296
  have eq64723 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq64716
  have eq64726 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq64723
       have r₂ := eq27
       grind)
    | exact resolve eq64723 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64723
  have eq64731 : x = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq64726
       grind)
    | exact superpose eq64726 eq50
    | exact resolve eq50 eq64726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64732 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq64726
       grind)
    | exact superpose eq64726 eq53
    | exact resolve eq53 eq64726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq70541 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq595 X0 X1 X2 X3 X4 x
       have i₂ := eq490 X4 X3 X2 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) x
       grind)
    | exact superpose eq490 eq595
    | exact resolve eq595 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq595
  have eq70542 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq70541 X0 X1 X2 X3 X4
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq70541
    | exact resolve eq70541 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq70541
  have eq71089 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op X1 (M.op (M.op X2 y) (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70542 X0 X1 X2 y x
       have i₂ := eq64726
       grind)
    | exact superpose eq64726 eq70542
    | exact resolve eq70542 eq64726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64726 eq70542
  have eq71946 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq71089 X0 X1 x
       have i₂ := eq6275 sF0 X1
       grind)
    | (have i₁ := eq71089 X0 X1 X1
       have i₂ := eq6275 sF0 X1
       grind)
    | exact superpose eq6275 eq71089
    | (have j0 := eq71089 X0 X1 x
       grind)
    | exact resolve eq71089 eq6275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6275 eq71089
  have eq78025 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq64732 eq71946
    | exact resolve eq71946 eq64732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71946
  have eq78682 : x = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq64731
       have i₂ := eq78025 (M.op sF0 sF0)
       grind)
    | exact superpose eq78025 eq64731
    | exact resolve eq64731 eq78025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64731
  have eq78706 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq78025 y
       grind)
    | exact superpose eq78025 eq122
    | exact resolve eq122 eq78025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq78025
  have eq79042 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78706
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78706
    | exact resolve eq78706 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq78706
  have eq79054 : x = y := by
    first
    | exact superpose eq64732 eq78682
    | exact resolve eq78682 eq64732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64732 eq78682
  have eq79131 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq79042
    | exact resolve eq79042 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq79042
  have eq79190 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq79054
       grind)
    | exact superpose eq79054 eq24
    | exact resolve eq24 eq79054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq79054
  have eq79307 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq79190
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq79190
    | exact resolve eq79190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq79190
  have eq79315 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq79307 eq26
    | exact resolve eq26 eq79307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq80168 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq79307 eq79131
    | exact resolve eq79131 eq79307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79131 eq79307
  have eq80893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80168 eq79315
    | exact resolve eq79315 eq80168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79315 eq80168
  have eq80894 : False := by grind
  exact eq80894

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq48
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq43 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq43 X0 X1
       grind)
    | exact resolve eq53 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq53
  have eq140 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq145 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       have j1 := eq56 X1 X0
       grind)
    | (have r₁ := eq140 X1 X0
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq140 X1 X1
       have r₂ := eq56 X1 X1
       grind)
    | exact resolve eq140 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq140
  have eq217 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq145 (σ X1) (σ X0)
       grind)
    | exact superpose eq145 eq15
    | exact resolve eq15 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1
       have i₂ := eq145 X1 X0
       grind)
    | exact superpose eq145 eq217
    | exact resolve eq217 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq217
  have eq224 : False := by grind
  exact eq224

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pxy_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq78 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq77
    | exact resolve eq77 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq77119 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq14
    | exact resolve eq14 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq77274 : x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq77119 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq77119
    | exact resolve eq77119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77119
  have eq77275 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq77274
  have eq77414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq77275 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77275
  have eq77426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq77414
    | exact resolve eq77414 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77414
  have eq77439 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq77426
       have r₂ := eq28
       grind)
    | exact resolve eq77426 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77426
  have eq77478 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op (σ y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq77439 eq14
    | exact resolve eq14 eq77439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77439
  have eq77633 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq77478 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq77478
    | exact resolve eq77478 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77478
  have eq77634 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq77633
  have eq77743 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq77634 eq30
    | exact resolve eq30 eq77634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq77634
  have eq77899 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq77743
    | exact resolve eq77743 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq77743
  have eq77900 : x = y := by grind
  clear eq77899
  have eq78222 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq77900
       grind)
    | exact superpose eq77900 eq19
    | exact resolve eq19 eq77900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq78223 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq77900
       grind)
    | exact superpose eq77900 eq25
    | exact resolve eq25 eq77900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq77900
  have eq78375 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq78223
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq78223
    | exact resolve eq78223 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq78223
  have eq78394 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq78375 eq27
    | exact resolve eq27 eq78375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq78375
  have eq79469 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq78394 eq70
    | exact resolve eq70 eq78394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq78394
  have eq79633 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq79469
       have i₂ := eq78222
       grind)
    | exact superpose eq78222 eq79469
    | exact resolve eq79469 eq78222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78222 eq79469
  have eq79674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq79633 eq15
    | exact resolve eq15 eq79633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79633
  have eq79755 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq79674
    | exact resolve eq79674 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq79674
  have eq79776 : False := by grind
  exact eq79776
