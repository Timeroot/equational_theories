import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_y_pxy_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  clear eq22
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
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
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3))) = (M.op X1 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X2) X1 X2
       have i₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq44
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq44 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq110 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq114 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq71 sF3
       grind)
    | exact superpose eq71 eq110
    | exact resolve eq110 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq116 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq71 y
       grind)
    | exact superpose eq71 eq114
    | exact resolve eq114 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq135 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq16
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq150 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq153 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq150
       have i₂ := eq71 sF1
       grind)
    | exact superpose eq71 eq150
    | exact resolve eq150 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq155 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq153
       have i₂ := eq71 sF0
       grind)
    | exact superpose eq71 eq153
    | exact resolve eq153 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq153
  have eq275 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq55 x X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq2035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq103 eq83
    | (have j0 := eq83 x (σ y)
       grind)
    | exact resolve eq83 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq103
  have eq2036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq2035
    | exact resolve eq2035 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq2039 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2036
       have r₂ := eq27
       grind)
    | exact resolve eq2036 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq2044 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2039 eq135
    | exact resolve eq135 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq2039
  have eq2070 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq2044
    | exact resolve eq2044 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2044
  have eq2071 : y = (M.op y y) := by grind
  clear eq2070
  have eq2073 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq2071
       have i₂ := eq275 y X0
       grind)
    | (have i₁ := eq2071
       have i₂ := eq275 X0 y
       grind)
    | exact superpose eq275 eq2071
    | exact resolve eq2071 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq2071
  have eq2166 : y = (M.op x y) := by
    first
    | (have i₁ := eq51 sF0
       have i₂ := eq2073 sF0
       grind)
    | exact superpose eq2073 eq51
    | exact resolve eq51 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2176 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq155
       have i₂ := eq2073 sF0
       grind)
    | exact superpose eq2073 eq155
    | exact resolve eq155 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq2188 : y = (σ y) := by
    first
    | (have i₁ := eq2176
       have i₂ := eq2073 sF1
       grind)
    | exact superpose eq2073 eq2176
    | exact resolve eq2176 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2195 : y = (M.op x y) := by
    first
    | (have i₁ := eq2166
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2166
    | exact resolve eq2166 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2166
  have eq2222 : y = (σ y) := by
    first
    | (have i₁ := eq2188
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2188
    | exact resolve eq2188 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188
  have eq2231 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2195 eq20
    | exact resolve eq20 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2251 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2231
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2231
    | exact resolve eq2231 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2231
  have eq2256 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq2222 eq26
    | exact resolve eq26 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2276 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq2195 eq279
    | exact resolve eq279 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq2195
  have eq2277 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2276 X0 X1
       have i₂ := eq284 X0 X0
       grind)
    | exact superpose eq284 eq2276
    | exact resolve eq2276 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq2276
  have eq2278 : ∀ X1 : G, y = (M.op x (M.op X1 y)) := by
    intro X1
    first
    | (have i₁ := eq2277 x X1
       have i₂ := eq2073 x
       grind)
    | exact superpose eq2073 eq2277
    | exact resolve eq2277 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073 eq2277
  have eq2279 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq2222 eq2251
    | exact resolve eq2251 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222 eq2251
  have eq2348 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) y)) = (M.op X0 (M.op x (M.op (M.op X0 X1) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X1 x (M.op X1 y)
       have i₂ := eq2278 X1
       grind)
    | exact superpose eq2278 eq56
    | exact resolve eq56 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2356 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2348 X0 x
       have i₂ := eq2278 (M.op X0 x)
       grind)
    | exact superpose eq2278 eq2348
    | exact resolve eq2348 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278 eq2348
  have eq2714 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2256
       have i₂ := eq2356 sF2
       grind)
    | exact superpose eq2356 eq2256
    | exact resolve eq2256 eq2356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256 eq2356
  have eq2717 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq2714 eq27
    | exact resolve eq27 eq2714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2714
  have eq2727 : False := by grind
  exact eq2727

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 X1
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq84 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq61 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq61 X0 (M.op X2 X0) X2
       have r₂ := eq12 (M.op X2 X0) (M.op X2 X0)
       grind)
    | (have r₁ := eq61 (M.op X1 X1) X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq61 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq61 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq157 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq159 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq157 X0 X1
       have j1 := eq84 X1 X1 X0
       grind)
    | (have r₁ := eq157 X0 X0
       have r₂ := eq84 X0 X0 X0
       grind)
    | (have r₁ := eq157 x X1
       have r₂ := eq84 X1 X1 x
       grind)
    | exact resolve eq157 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq157
  have eq987 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq159 (σ X0) (σ X1)
       grind)
    | exact superpose eq159 eq15
    | exact resolve eq15 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq987 X0 X1
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq987
    | exact resolve eq987 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq987
  have eq1003 : False := by grind
  exact eq1003

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq234 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2938 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq234 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq234 X0 X1
       grind)
    | exact superpose eq234 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq234 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq234 X0 X1
       grind)
    | exact resolve eq12 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2939 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq234 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq234 X0 X1
       grind)
    | exact superpose eq234 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq234 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq234 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq234 X0 X1
       grind)
    | exact resolve eq13 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq2952 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2939 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939
  have eq2960 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2952 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2952 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq2952 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq2952 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952
  have eq2961 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2938 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2938 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq2938 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq2978 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2960 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2960
    | (have j0 := eq2960 X0 X1
       grind)
    | exact resolve eq2960 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960
  have eq2979 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2978 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978
  have eq2980 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2961 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2961
    | (have j0 := eq2961 X0 X1
       grind)
    | exact resolve eq2961 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2961
  have eq2981 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2980 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980
  have eq2991 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2981 X0 X1
       have j1 := eq2979 X0 X1
       grind)
    | (have r₁ := eq2981 X0 X1
       have r₂ := eq2979 X0 X1
       grind)
    | exact resolve eq2981 eq2979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2979 eq2981
  have eq3003 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2991 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2991
    | exact resolve eq2991 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3036 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2991 x y
       grind)
    | exact superpose eq2991 eq16
    | exact resolve eq16 eq2991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2991
  have eq3438 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq3003 X0 (τ X1)
       grind)
    | exact superpose eq3003 eq18
    | exact resolve eq18 eq3003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3003
  have eq3451 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3438 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3438
    | exact resolve eq3438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438
  have eq3473 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3451 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3451
    | exact resolve eq3451 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451
  have eq3513 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq3036
       have i₂ := eq3473 x y
       grind)
    | exact superpose eq3473 eq3036
    | exact resolve eq3036 eq3473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036 eq3473
  have eq3514 : False := by grind
  exact eq3514

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  clear eq22
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
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
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X2)) ∨ (k (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X2) (M.op X1 X2)) X1
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq44
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq44 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114 eq79
    | (have j0 := eq79 (σ x) (σ y)
       grind)
    | exact resolve eq79 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq128
       have r₂ := eq27
       grind)
    | exact resolve eq128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq133 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq131
    | exact resolve eq131 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq224 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq133 eq52
    | exact resolve eq52 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq250 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq236
    | (have j0 := eq236 (σ x)
       grind)
    | exact resolve eq236 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq250
    | exact resolve eq250 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq267 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq262
  have eq268 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq267
    | exact resolve eq267 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq275 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq236 X0
       grind)
    | exact superpose eq236 eq55
    | exact resolve eq55 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq288 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq295 : ∀ X1 : G, (M.op X1 X1) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq275 X1 X1
       have i₂ := eq14 sF2 X1 sF3
       grind)
    | exact superpose eq14 eq275
    | exact resolve eq275 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq305 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X1
       have i₂ := eq295 sF2
       grind)
    | exact superpose eq295 eq295
    | exact resolve eq295 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq268
       have i₂ := eq295 sF2
       grind)
    | exact superpose eq295 eq268
    | exact resolve eq268 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq295
  have eq324 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq319 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq328 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq332 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq324 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq324
    | exact resolve eq324 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq324 X0
       grind)
    | exact superpose eq324 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq324 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq324 X0
       grind)
    | exact resolve eq13 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq332 sF0
       have i₂ := eq328 sF0 x
       grind)
    | (have i₁ := eq332 sF0
       have i₂ := eq328 X0 sF0
       grind)
    | exact superpose eq328 eq332
    | exact resolve eq332 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq332
  have eq969 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq6271 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq346 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq6273 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq6271
    | exact resolve eq6271 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq6271
  have eq6282 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6273
  have eq6594 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6282 eq89
    | exact resolve eq89 eq6282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq6282
  have eq6601 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq6594
    | exact resolve eq6594 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6594
  have eq6604 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79 y y
       have i₂ := eq6601
       grind)
    | exact superpose eq6601 eq79
    | (have j0 := eq79 y y
       grind)
    | exact resolve eq79 eq6601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6601
  have eq6605 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq6604
  have eq6621 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq324 y
       have i₂ := eq6605
       grind)
    | exact superpose eq6605 eq324
    | exact resolve eq324 eq6605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq6628 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq969 y
       have i₂ := eq6605
       grind)
    | exact superpose eq6605 eq969
    | exact resolve eq969 eq6605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq6605
  have eq6651 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6628
  have eq6657 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6621
  have eq6665 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6651
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6651
    | exact resolve eq6651 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6651
  have eq6800 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6665 eq6657
    | exact resolve eq6657 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6657 eq6665
  have eq6801 : y = (M.op x y) := by grind
  clear eq6800
  have eq6827 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq6801 eq20
    | exact resolve eq20 eq6801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq6845 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6827
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6827
    | exact resolve eq6827 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6827
  have eq6847 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq6845 eq26
    | exact resolve eq26 eq6845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq6975 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq6801 eq224
    | exact resolve eq224 eq6801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq7109 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq51 eq6975
    | exact resolve eq6975 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq6975
  have eq7184 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7109 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7109
    | (have j0 := eq7109 X0
       grind)
    | exact resolve eq7109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7109
  have eq7216 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq6801 eq7184
    | exact resolve eq7184 eq6801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7184
  have eq7221 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7216 X0
       have i₂ := eq288 X0 X0
       grind)
    | exact superpose eq288 eq7216
    | exact resolve eq7216 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq7216
  have eq7223 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7221 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7221
    | (have j0 := eq7221 X0
       grind)
    | exact resolve eq7221 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7221
  have eq7225 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq6801 eq7223
    | exact resolve eq7223 eq6801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801 eq7223
  have eq7326 : ∀ X1 : G, y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op x x) x
       have i₂ := eq7225 (M.op x x)
       grind)
    | exact superpose eq7225 eq54
    | exact resolve eq54 eq7225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq7332 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq69 (M.op x x) x x
       have i₂ := eq7225 (M.op x x)
       grind)
    | exact superpose eq7225 eq69
    | exact resolve eq69 eq7225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq7385 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq7332 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7332
  have eq7540 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq7385 y
       grind)
    | exact superpose eq7385 eq77
    | exact resolve eq77 eq7385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7385
  have eq7543 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7540
       have i₂ := eq7225 y
       grind)
    | exact superpose eq7225 eq7540
    | exact resolve eq7540 eq7225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7540
  have eq7547 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6845 eq7543
    | exact resolve eq7543 eq6845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7543
  have eq7550 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7547
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7547
    | exact resolve eq7547 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7547
  have eq7552 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6845 eq7550
    | exact resolve eq7550 eq6845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845 eq7550
  have eq7557 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7552 eq79
    | (have j0 := eq79 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq79 eq7552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq7552
  have eq7558 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq7557
  have eq7560 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq7558
       have i₂ := eq7225 sF1
       grind)
    | exact superpose eq7225 eq7558
    | exact resolve eq7558 eq7225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7225 eq7558
  have eq7574 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq7560 eq6847
    | exact resolve eq6847 eq7560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6847
  have eq7577 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7574
       have i₂ := eq7326 sF2
       grind)
    | exact superpose eq7326 eq7574
    | exact resolve eq7574 eq7326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7326 eq7574
  have eq7613 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq7577 eq27
    | exact resolve eq27 eq7577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7577
  have eq7649 : False := by grind
  exact eq7649

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  clear eq22
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
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
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X2)) ∨ (k (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X2) (M.op X1 X2)) X1
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq44
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq44 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114 eq79
    | (have j0 := eq79 (σ x) (σ y)
       grind)
    | exact resolve eq79 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq128
       have r₂ := eq27
       grind)
    | exact resolve eq128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq133 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq131
    | exact resolve eq131 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq224 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq133 eq52
    | exact resolve eq52 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq252 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq237
    | (have j0 := eq237 (σ x)
       grind)
    | exact resolve eq237 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq252
    | exact resolve eq252 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq270 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq265
  have eq271 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq270
    | exact resolve eq270 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq278 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq237 X0
       grind)
    | exact superpose eq237 eq55
    | exact resolve eq55 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq291 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq299 : ∀ X1 : G, (M.op X1 X1) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq278 X1 X1
       have i₂ := eq14 sF2 X1 sF3
       grind)
    | exact superpose eq14 eq278
    | exact resolve eq278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq309 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq299 X1
       have i₂ := eq299 sF2
       grind)
    | exact superpose eq299 eq299
    | exact resolve eq299 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq271
       have i₂ := eq299 sF2
       grind)
    | exact superpose eq299 eq271
    | exact resolve eq271 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq299
  have eq328 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq332 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq336 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq328 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq328
    | exact resolve eq328 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq328 X0
       grind)
    | exact superpose eq328 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq328 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq328 X0
       grind)
    | exact resolve eq13 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq336 sF0
       have i₂ := eq332 sF0 x
       grind)
    | (have i₁ := eq336 sF0
       have i₂ := eq332 X0 sF0
       grind)
    | exact superpose eq332 eq336
    | exact resolve eq336 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq336
  have eq976 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq962 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq6325 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq350 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq6637 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq6325
    | exact resolve eq6325 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq6325
  have eq6646 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6637
  have eq6649 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6646 eq89
    | exact resolve eq89 eq6646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq6646
  have eq6656 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq6649
    | exact resolve eq6649 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6649
  have eq6659 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79 y y
       have i₂ := eq6656
       grind)
    | exact superpose eq6656 eq79
    | (have j0 := eq79 y y
       grind)
    | exact resolve eq79 eq6656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6656
  have eq6660 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq6659
  have eq6676 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq328 y
       have i₂ := eq6660
       grind)
    | exact superpose eq6660 eq328
    | exact resolve eq328 eq6660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq6683 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq976 y
       have i₂ := eq6660
       grind)
    | exact superpose eq6660 eq976
    | exact resolve eq976 eq6660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976 eq6660
  have eq6706 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6683
  have eq6712 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6676
  have eq6720 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6706
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6706
    | exact resolve eq6706 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6706
  have eq6855 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6720 eq6712
    | exact resolve eq6712 eq6720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6712 eq6720
  have eq6856 : y = (M.op x y) := by grind
  clear eq6855
  have eq6882 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq6856 eq20
    | exact resolve eq20 eq6856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq6900 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6882
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6882
    | exact resolve eq6882 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6882
  have eq6902 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq6900 eq26
    | exact resolve eq26 eq6900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq7031 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq6856 eq224
    | exact resolve eq224 eq6856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq7165 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq51 eq7031
    | exact resolve eq7031 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq7031
  have eq7243 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7165 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7165
    | (have j0 := eq7165 X0
       grind)
    | exact resolve eq7165 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7165
  have eq7276 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq6856 eq7243
    | exact resolve eq7243 eq6856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7243
  have eq7281 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7276 X0
       have i₂ := eq291 X0 X0
       grind)
    | exact superpose eq291 eq7276
    | exact resolve eq7276 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq7276
  have eq7283 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7281 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7281
    | (have j0 := eq7281 X0
       grind)
    | exact resolve eq7281 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7281
  have eq7285 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq6856 eq7283
    | exact resolve eq7283 eq6856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6856 eq7283
  have eq7386 : ∀ X1 : G, y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op x x) x
       have i₂ := eq7285 (M.op x x)
       grind)
    | exact superpose eq7285 eq54
    | exact resolve eq54 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq7392 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq69 (M.op x x) x x
       have i₂ := eq7285 (M.op x x)
       grind)
    | exact superpose eq7285 eq69
    | exact resolve eq69 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq7445 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq7392 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7392
  have eq7603 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq7445 y
       grind)
    | exact superpose eq7445 eq77
    | exact resolve eq77 eq7445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7445
  have eq7606 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7603
       have i₂ := eq7285 y
       grind)
    | exact superpose eq7285 eq7603
    | exact resolve eq7603 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7603
  have eq7610 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6900 eq7606
    | exact resolve eq7606 eq6900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7606
  have eq7613 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7610
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7610
    | exact resolve eq7610 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7610
  have eq7615 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6900 eq7613
    | exact resolve eq7613 eq6900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6900 eq7613
  have eq7620 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7615 eq79
    | (have j0 := eq79 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq79 eq7615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq7615
  have eq7621 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq7620
  have eq7623 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq7621
       have i₂ := eq7285 sF1
       grind)
    | exact superpose eq7285 eq7621
    | exact resolve eq7621 eq7285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7285 eq7621
  have eq7637 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq7623 eq6902
    | exact resolve eq6902 eq7623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6902
  have eq7640 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7637
       have i₂ := eq7386 sF2
       grind)
    | exact superpose eq7386 eq7637
    | exact resolve eq7637 eq7386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7386 eq7637
  have eq7676 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq7640 eq27
    | exact resolve eq27 eq7640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7640
  have eq7712 : False := by grind
  exact eq7712

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq64 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq47 (τ X0)
       grind)
    | exact superpose eq47 eq19
    | exact resolve eq19 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq67 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq67
    | exact resolve eq67 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq67
  have eq85 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85
    | (have j0 := eq85 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq85 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X1
       have i₂ := eq27 X0 (τ X1)
       grind)
    | exact superpose eq27 eq73
    | exact resolve eq73 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq357 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq117 x X1
       have i₂ := eq27 x X0
       grind)
    | exact superpose eq27 eq117
    | exact resolve eq117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq117
  have eq401 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq16
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq817 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq401
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq401
    | (have j1 := eq85 (σ x) (σ y)
       grind)
    | (have r₁ := eq401
       have r₂ := eq85 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq401
       have r₂ := eq85 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq401 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq401
  have eq818 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq817
  have eq819 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq16
    | exact resolve eq16 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq820 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq819
       have r₂ := eq357 x (σ x)
       grind)
    | exact resolve eq819 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq822 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq820
       grind)
    | exact superpose eq820 eq10
    | exact resolve eq10 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq834 : x = y := by
    first
    | (have i₁ := eq822
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq822
    | exact resolve eq822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq836 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq834
       grind)
    | exact superpose eq834 eq16
    | exact resolve eq16 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq837 : False := by grind
  exact eq837

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_y_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq33 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq34 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq28 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28
    | (have j0 := eq28 y
       grind)
    | exact resolve eq28 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq66 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq56 X0 X2
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq103 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X0 X1 X2
       have i₂ := eq55 X0 X0 X1
       grind)
    | exact superpose eq55 eq95
    | exact resolve eq95 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq95
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq98 X0 X0
       grind)
    | exact superpose eq98 eq93
    | exact resolve eq93 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq139 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq53
    | exact resolve eq53 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq204 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X2 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 X3 X4
       have i₂ := eq103 X1 X2 X0
       grind)
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq103 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq98 X3 X2
       have i₂ := eq103 X1 X2 X0
       grind)
    | (have i₁ := eq98 X0 (M.op X0 X0)
       have i₂ := eq103 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq103 eq98
    | exact resolve eq98 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq211 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) X1 X2
       have i₂ := eq103 X0 (M.op X1 X2) X2
       grind)
    | (have i₁ := eq9 X2 X0 X0
       have i₂ := eq103 X0 X1 X2
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq232 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq237 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq12
    | (have r₁ := eq12 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq92 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq92 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq61 eq243
    | exact resolve eq243 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq245 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq66 eq256
    | exact resolve eq256 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq275 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x y))) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq105 X1 X0
       grind)
    | exact superpose eq105 eq53
    | exact resolve eq53 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x y))) = (M.op X1 (M.op x (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 x) X1 x
       have i₂ := eq105 (M.op X1 x) X1
       grind)
    | exact superpose eq105 eq9
    | exact resolve eq9 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 : G, (k (σ (σ X0)) X1) = (σ (σ (k X0 (τ (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (σ X0)
       have i₂ := eq48 (τ X1) X0
       grind)
    | exact superpose eq48 eq48
    | exact resolve eq48 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq356 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq317 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq317
    | exact resolve eq317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq1180 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq1190 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq33
       have i₂ := eq14 sF1 sF2
       grind)
    | exact superpose eq14 eq33
    | (have j1 := eq14 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq33 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1192 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1193 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq14 (σ X0) sF3
       grind)
    | exact superpose eq14 eq35
    | (have j1 := eq14 (σ X0) (σ y)
       grind)
    | exact resolve eq35 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1195 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq1204 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1195
    | exact resolve eq1195 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1205 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1192
    | exact resolve eq1192 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1214 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1204
    | exact resolve eq1204 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1215 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1205
       have r₂ := eq244
       grind)
    | exact resolve eq1205 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1238 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq237 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1440 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (σ (k X0 (τ (τ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (σ X0) X1
       have i₂ := eq310 X0 (σ X1)
       grind)
    | exact superpose eq310 eq15
    | exact resolve eq15 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq1462 : ∀ X0 X1 : G, (σ (σ (k X0 (τ X1)))) = (σ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1440 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1440
    | exact resolve eq1440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq3780 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1214
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1214
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq1214 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3780
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3780
    | exact resolve eq3780 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3780
  have eq3791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq3790
    | exact resolve eq3790 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790
  have eq3792 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq3791
       have r₂ := eq27
       grind)
    | exact resolve eq3791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq3793 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3792
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3792
    | exact resolve eq3792 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3792
  have eq3795 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3793 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3793
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3793
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3793
       grind)
    | exact resolve eq12 eq3793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3793
  have eq3805 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq3795
  have eq3808 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq66 eq3805
    | exact resolve eq3805 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq3810 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq3808
    | exact resolve eq3808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq4181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3810
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq3810
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq3810 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3810
  have eq4191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq4181
  have eq4193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4191
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4191
    | exact resolve eq4191 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4191
  have eq4194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4193
    | exact resolve eq4193 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193
  have eq4195 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4194
       have r₂ := eq27
       grind)
    | exact resolve eq4194 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4194
  have eq4196 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4195
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4195
    | exact resolve eq4195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4195
  have eq4197 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4196
  have eq4199 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq4197
       grind)
    | exact superpose eq4197 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4197
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4197
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4197
       grind)
    | exact resolve eq12 eq4197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4197
  have eq4210 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4199
  have eq4213 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4210
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4210
    | exact resolve eq4210 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4210
  have eq4223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1214
       have i₂ := eq4213
       grind)
    | exact superpose eq4213 eq1214
    | exact resolve eq1214 eq4213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq4226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4223
  have eq4228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4226
    | exact resolve eq4226 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq4229 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4228
       have r₂ := eq27
       grind)
    | exact resolve eq4228 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228
  have eq4231 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4229 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4229
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4229
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4229
       grind)
    | exact resolve eq12 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4229
  have eq4242 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4231
  have eq4245 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66 eq4242
    | exact resolve eq4242 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4242
  have eq4247 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4245
    | exact resolve eq4245 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4245
  have eq4275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4247
       have i₂ := eq4213
       grind)
    | exact superpose eq4213 eq4247
    | exact resolve eq4247 eq4213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213 eq4247
  have eq4288 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4275
  have eq4290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4288
    | exact resolve eq4288 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288
  have eq4292 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4290
       have r₂ := eq27
       grind)
    | exact resolve eq4290 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4290
  have eq4293 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4292 eq257
    | (have r₁ := eq257
       have r₂ := eq4292
       grind)
    | exact resolve eq257 eq4292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq4295 : (σ x) ≠ (σ x) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4292 eq244
    | (have r₁ := eq244
       have r₂ := eq4292
       grind)
    | exact resolve eq244 eq4292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq4296 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4292 eq27
    | exact resolve eq27 eq4292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4292
  have eq4297 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4295
  have eq4298 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4293
  have eq4319 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4297
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq4297
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq4297 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4340 : x = (M.op x y) ∨ (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4319
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4319
    | exact resolve eq4319 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319
  have eq4341 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq4340
  have eq4363 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1180 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1238 X0
       grind)
    | exact superpose eq1238 eq1180
    | (have j0 := eq1180 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq1180 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4434 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq1180 X0 X1
       grind)
    | exact superpose eq1180 eq10
    | (have j1 := eq1180 X0 X1
       grind)
    | exact resolve eq10 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4458 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq4363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363
  have eq4492 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op x (M.op (σ (M.op X0 X0)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4458 X0
       have i₂ := eq53 (σ (M.op X0 X0))
       grind)
    | exact superpose eq53 eq4458
    | exact resolve eq4458 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4458
  have eq4671 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4298
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq4298
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq4298 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4680 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq4298
       grind)
    | exact superpose eq4298 eq10
    | exact resolve eq10 eq4298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4705 : y = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq4680
    | exact resolve eq4680 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4680
  have eq4708 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4671
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4671
    | exact resolve eq4671 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq4711 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq4708
    | exact resolve eq4708 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4708
  have eq4714 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4711
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4711
    | exact resolve eq4711 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4711
  have eq4715 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq4714
  have eq4732 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq4705
       grind)
    | exact superpose eq4705 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq4705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4742 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4732
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4732
    | exact resolve eq4732 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4732
  have eq4745 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4742
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4742
    | exact resolve eq4742 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4742
  have eq4746 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq4745
  have eq6468 : (M.op y x) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op y x)
       have i₂ := eq4341
       grind)
    | exact superpose eq4341 eq10
    | exact resolve eq10 eq4341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq6661 : (τ (σ y)) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4746 eq6468
    | exact resolve eq6468 eq4746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4746
  have eq6662 : (τ (σ y)) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4715 eq6468
    | exact resolve eq6468 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4715 eq6468
  have eq6709 : (τ (σ y)) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6662
  have eq6710 : (τ (σ y)) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq6661
  have eq6715 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39 eq6709
    | exact resolve eq6709 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6709
  have eq6716 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6715
  have eq6717 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39 eq6710
    | exact resolve eq6710 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6710
  have eq6718 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6717
  have eq6722 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6716
       grind)
    | exact superpose eq6716 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq6716
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6716
       grind)
    | exact resolve eq12 eq6716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6723 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6716
       grind)
    | exact superpose eq6716 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6716
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6716
       grind)
    | exact resolve eq13 eq6716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6716
  have eq6732 : x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6723
  have eq6733 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6722
  have eq6736 : x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6732
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6732
    | exact resolve eq6732 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6732
  have eq6737 : x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6736
  have eq6738 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6733
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6733
    | exact resolve eq6733 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6733
  have eq6742 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6718
       grind)
    | exact superpose eq6718 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq6718
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6718
       grind)
    | exact resolve eq12 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6743 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6718
       grind)
    | exact superpose eq6718 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6718
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6718
       grind)
    | exact resolve eq13 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6718
  have eq6752 : x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6743
  have eq6753 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6742
  have eq6756 : x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6752
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6752
    | exact resolve eq6752 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6752
  have eq6757 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6756
  have eq6758 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6753
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6753
    | exact resolve eq6753 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753
  have eq6763 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq4297
       have i₂ := eq6737
       grind)
    | exact superpose eq6737 eq4297
    | exact resolve eq4297 eq6737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6737
  have eq6779 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6763
  have eq6785 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6779
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6779
    | exact resolve eq6779 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6779
  have eq6796 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq4298
       have i₂ := eq6738
       grind)
    | exact superpose eq6738 eq4298
    | exact resolve eq4298 eq6738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4298
  have eq6802 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6796
  have eq6810 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq6802
    | exact resolve eq6802 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6802
  have eq6811 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6810
  have eq7113 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4297
       have i₂ := eq6757
       grind)
    | exact superpose eq6757 eq4297
    | exact resolve eq4297 eq6757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4297 eq6757
  have eq7129 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7113
  have eq7135 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7129
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7129
    | exact resolve eq7129 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7129
  have eq7147 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4705
       have i₂ := eq6758
       grind)
    | exact superpose eq6758 eq4705
    | exact resolve eq4705 eq6758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4705 eq6758
  have eq7151 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq7147
  have eq7263 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6811 eq6785
    | exact resolve eq6785 eq6811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6785
  have eq7266 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6811 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6811
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6811
       grind)
    | exact resolve eq12 eq6811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6811
  have eq7277 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7266
  have eq7279 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq7263
  have eq7296 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66 eq7277
    | exact resolve eq7277 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq7277
  have eq7311 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7296
    | exact resolve eq7296 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7296
  have eq7316 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7279 eq39
    | exact resolve eq39 eq7279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7279
  have eq7394 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq7316
    | exact resolve eq7316 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq7316
  have eq7406 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7394 eq39
    | exact resolve eq39 eq7394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7394
  have eq7461 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq37 eq7406
    | exact resolve eq7406 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7406
  have eq7600 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7151 eq7135
    | exact resolve eq7135 eq7151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7135 eq7151
  have eq7616 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7600
  have eq8042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq7311
       have i₂ := eq6738
       grind)
    | exact superpose eq6738 eq7311
    | exact resolve eq7311 eq6738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6738 eq7311
  have eq8071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8042
  have eq8075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8071
    | exact resolve eq8071 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8071
  have eq8079 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8075
       have r₂ := eq27
       grind)
    | exact resolve eq8075 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8075
  have eq8083 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8079 eq26
    | exact resolve eq26 eq8079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8118 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8079 eq7616
    | exact resolve eq7616 eq8079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7616 eq8079
  have eq8119 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq8118
  have eq8145 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8119
       have r₂ := eq4296
       grind)
    | exact resolve eq8119 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296 eq8119
  have eq8158 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8145 eq105
    | exact resolve eq105 eq8145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8176 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq8145
  have eq10040 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8158 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8158
    | (have j0 := eq8158 X0 x
       grind)
    | exact resolve eq8158 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8158
  have eq10201 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq7461 eq10040
    | exact resolve eq10040 eq7461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7461 eq10040
  have eq10304 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10201 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10201
  have eq10320 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10304 X0
       grind)
    | (have r₁ := eq10304 X0
       have r₂ := eq8176
       grind)
    | exact resolve eq10304 eq8176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8176 eq10304
  have eq10323 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10320 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10320
    | (have j0 := eq10320 X0
       grind)
    | exact resolve eq10320 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10320
  have eq10371 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1238 x
       have i₂ := eq10323 x
       grind)
    | exact superpose eq10323 eq1238
    | exact resolve eq1238 eq10323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq10323
  have eq10452 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10371 eq1180
    | (have j0 := eq1180 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1180 eq10371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq10371
  have eq10456 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq10452
  have eq10472 : (σ (M.op x y)) = (M.op x (M.op (σ (M.op x y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10456
       have i₂ := eq53 (σ sF0)
       grind)
    | exact superpose eq53 eq10456
    | exact resolve eq10456 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq10456
  have eq10481 : (σ (M.op x y)) = (M.op x (M.op (σ (M.op x y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq10472
    | exact resolve eq10472 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10472
  have eq12050 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10481 eq285
    | exact resolve eq285 eq10481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10481
  have eq12964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12050 eq8083
    | exact resolve eq8083 eq12050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8083 eq12050
  have eq12967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12964
  have eq12986 : x = (M.op x y) := by
    first
    | (have r₁ := eq12967
       have r₂ := eq27
       grind)
    | exact resolve eq12967 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12967
  have eq12991 : x = (M.op x y) := by
    first
    | exact superpose eq12986 eq18
    | exact resolve eq18 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq12992 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq12986 eq20
    | exact resolve eq20 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq12997 : (k (σ (M.op x y)) (σ y)) = (σ (k x y)) := by
    first
    | exact superpose eq12986 eq34
    | exact resolve eq34 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq12998 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq12986 eq37
    | exact resolve eq37 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq13003 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 x)) := by
    intro X0 X1
    first
    | exact superpose eq12986 eq105
    | exact resolve eq105 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq13004 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq12986 eq139
    | exact resolve eq139 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq13007 : x ≠ x ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq12986 eq232
    | (have r₁ := eq232
       have r₂ := eq12986
       grind)
    | exact resolve eq232 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq13010 : x ≠ x ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq12986 eq245
    | (have r₁ := eq245
       have r₂ := eq12986
       grind)
    | exact resolve eq245 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq13013 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op x (M.op X1 x)) := by
    intro X0 X1
    first
    | exact superpose eq12986 eq275
    | exact resolve eq275 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq13015 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op X1 (M.op x (M.op X0 x))) := by
    intro X0 X1
    first
    | exact superpose eq12986 eq285
    | exact resolve eq285 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq13036 : (σ (k x x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12986 eq1190
    | exact resolve eq1190 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq13200 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op x (M.op (σ (M.op X0 X0)) x)) := by
    intro X0
    first
    | exact superpose eq12986 eq4492
    | exact resolve eq4492 eq12986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492 eq12986
  have eq13349 : y = (k x y) ∨ y = (M.op y x) := by grind
  clear eq13010
  have eq13350 : (k y x) = (M.op y x) := by grind
  clear eq13007
  have eq13391 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1215
       have i₂ := eq13350
       grind)
    | exact superpose eq13350 eq1215
    | exact resolve eq1215 eq13350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215 eq13350
  have eq13423 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12992
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12992
    | exact resolve eq12992 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12992
  have eq13446 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13423 eq22
    | exact resolve eq22 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq13447 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13423 eq26
    | exact resolve eq26 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq13652 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq13423 eq13004
    | exact resolve eq13004 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13004
  have eq13656 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (k x x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq13423 eq13036
    | exact resolve eq13036 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13036
  have eq13697 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | exact superpose eq13423 eq13391
    | exact resolve eq13391 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13391
  have eq13753 : (M.op (σ y) (σ (M.op x y))) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq13423 eq13697
    | exact resolve eq13697 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13697
  have eq13768 : (σ (k x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq13423 eq13656
    | exact resolve eq13656 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13656
  have eq13869 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (k x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13423 eq13768
    | exact resolve eq13768 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13423 eq13768
  have eq13870 : (σ (k x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq13869
  have eq14299 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1193 x
       have i₂ := eq13349
       grind)
    | exact superpose eq13349 eq1193
    | (have j0 := eq1193 x
       grind)
    | exact resolve eq1193 eq13349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq14302 : (τ y) = (k (τ x) (τ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq356 x y
       have i₂ := eq13349
       grind)
    | exact superpose eq13349 eq356
    | exact resolve eq356 eq13349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13349
  have eq14306 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14299
       have i₂ := eq13446
       grind)
    | exact superpose eq13446 eq14299
    | exact resolve eq14299 eq13446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14299
  have eq14308 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13447 eq14306
    | exact resolve eq14306 eq13447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14306
  have eq14310 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14308
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14308
    | exact resolve eq14308 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14308
  have eq14312 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14310
       have i₂ := eq13446
       grind)
    | exact superpose eq13446 eq14310
    | exact resolve eq14310 eq13446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14310
  have eq14314 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13447 eq14312
    | exact resolve eq14312 eq13447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14312
  have eq14316 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq14314
       have r₂ := eq27
       grind)
    | exact resolve eq14314 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14314
  have eq14318 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14316
       have i₂ := eq13446
       grind)
    | exact superpose eq13446 eq14316
    | exact resolve eq14316 eq13446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14316
  have eq15408 : (k x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq13870
       grind)
    | exact superpose eq13870 eq10
    | exact resolve eq10 eq13870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13870
  have eq15423 : (σ y) ≠ (σ y) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14318 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq14318
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14318
       grind)
    | exact resolve eq12 eq14318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14318
  have eq15433 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq15423
  have eq15435 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13447 eq15433
    | exact resolve eq15433 eq13447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15433
  have eq15437 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12997 eq15435
    | exact resolve eq15435 eq12997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15435
  have eq15466 : (σ (k (σ (τ x)) y)) = (σ (σ (τ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1462 (τ x) y
       have i₂ := eq14302
       grind)
    | exact superpose eq14302 eq1462
    | exact resolve eq1462 eq14302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462 eq14302
  have eq15481 : (σ y) = (σ (k (σ (τ x)) y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq15466
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq15466
    | exact resolve eq15466 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15466
  have eq15494 : (σ y) = (σ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq15481
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq15481
    | exact resolve eq15481 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15481
  have eq15505 : (σ y) = (σ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq15494
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15494
    | exact resolve eq15494 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15494
  have eq15573 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq15408
       have i₂ := eq92 sF1 x
       grind)
    | (have i₁ := eq15408
       have i₂ := eq92 X0 sF1
       grind)
    | exact superpose eq92 eq15408
    | exact resolve eq15408 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15408
  have eq15617 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13015 (σ (M.op X0 X0)) X1
       have i₂ := eq13200 X0
       grind)
    | exact superpose eq13200 eq13015
    | exact resolve eq13015 eq13200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15620 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op x (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq13013 (σ (M.op X0 X0)) X1
       have i₂ := eq13200 X0
       grind)
    | exact superpose eq13200 eq13013
    | exact resolve eq13013 eq13200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15622 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13003 X1 (σ (M.op X0 X0))
       have i₂ := eq13200 X0
       grind)
    | exact superpose eq13200 eq13003
    | exact resolve eq13003 eq13200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13200
  have eq15660 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq15622 X2 x
       have i₂ := eq15622 X0 x
       grind)
    | exact superpose eq15622 eq15622
    | exact resolve eq15622 eq15622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15678 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15622 x X1
       have i₂ := eq15622 X0 x
       grind)
    | exact superpose eq15622 eq15622
    | exact resolve eq15622 eq15622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15688 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op x (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq15622 (M.op x (M.op X0 x)) X1
       have i₂ := eq13015 X0 (M.op x (M.op X0 x))
       grind)
    | exact superpose eq13015 eq15622
    | exact resolve eq15622 eq13015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15742 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq15622 X1 X0
       grind)
    | exact superpose eq15622 eq10
    | exact resolve eq10 eq15622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15836 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (τ (M.op X0 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15742 (M.op x x) X3
       have i₂ := eq204 (M.op x x) x X1 X0 X2
       grind)
    | exact superpose eq204 eq15742
    | exact resolve eq15742 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq15893 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (M.op X2 (τ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq211 (M.op x x) x X2
       have i₂ := eq15742 X0 (M.op x x)
       grind)
    | exact superpose eq15742 eq211
    | exact resolve eq211 eq15742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq15982 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15660 X1 x
       have i₂ := eq15622 X0 x
       grind)
    | exact superpose eq15622 eq15660
    | exact resolve eq15660 eq15622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15622 eq15660
  have eq16162 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq209 X1 X2 (M.op x x) x
       have i₂ := eq15678 X0 (M.op x x)
       grind)
    | exact superpose eq15678 eq209
    | exact resolve eq209 eq15678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq15678
  have eq16821 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (σ (M.op x (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq15620 (M.op x (M.op X0 x)) X1
       have i₂ := eq13015 X0 (M.op x (M.op X0 x))
       grind)
    | exact superpose eq13015 eq15620
    | exact resolve eq15620 eq13015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15620
  have eq18512 : ∀ X0 X2 : G, (σ (σ (M.op X2 X2))) = (σ (σ (M.op x (M.op X0 x)))) := by
    intro X0 X2
    first
    | (have i₁ := eq15982 X2 x
       have i₂ := eq15688 X0 x
       grind)
    | exact superpose eq15688 eq15982
    | exact resolve eq15982 eq15688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15688 eq15982
  have eq38155 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4434 X0 X0
       have i₂ := eq92 (σ X0) X1
       grind)
    | (have i₁ := eq4434 X0 X0
       have i₂ := eq92 X0 (σ X0)
       grind)
    | exact superpose eq92 eq4434
    | exact resolve eq4434 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq4434
  have eq38314 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq38155 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38155
  have eq58044 : ∀ X0 : G, (k x x) = (τ (σ (M.op X0 X0))) ∨ (σ (M.op x y)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15573 (σ (M.op X0 X0))
       have i₂ := eq15617 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq15617 eq15573
    | exact resolve eq15573 eq15617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15617
  have eq58075 : ∀ X0 X1 : G, (M.op X0 X0) = (k x x) ∨ (σ (M.op x y)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15742 X1 X0
       have i₂ := eq15573 X1
       grind)
    | exact superpose eq15573 eq15742
    | (have j1 := eq15573 X1
       grind)
    | exact resolve eq15742 eq15573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15573 eq15742
  have eq58193 : ∀ X0 : G, (M.op X0 X0) = (k x x) ∨ (σ (M.op x y)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58044 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq58044
    | (have j0 := eq58044 X0
       grind)
    | exact resolve eq58044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58044
  have eq58952 : ∀ X0 : G, (σ (M.op x y)) ≠ (k x x) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq58075 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58075
  have eq68401 : ∀ X0 : G, (M.op X0 X0) = (τ (σ (M.op x y))) ∨ (M.op X0 X0) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq58193 X0
       grind)
    | exact superpose eq58193 eq10
    | (have j1 := eq58193 X0
       grind)
    | exact resolve eq10 eq58193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58193
  have eq68455 : ∀ X0 : G, (M.op X0 X0) = x ∨ (M.op X0 X0) = (k x x) := by
    intro X0
    first
    | exact superpose eq12998 eq68401
    | (have j0 := eq68401 X0
       grind)
    | exact resolve eq68401 eq12998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12998 eq68401
  have eq68570 : ∀ X0 : G, (M.op X0 X0) = (k x x) := by
    intro X0
    first
    | (have j0 := eq68455 X0
       have j1 := eq237 X0 x
       grind)
    | (have r₁ := eq68455 X0
       have r₂ := eq237 X0 x
       grind)
    | (have r₁ := eq68455 X0
       have r₂ := eq237 X0 (k x x)
       grind)
    | exact resolve eq68455 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq68455
  have eq68739 : ∀ X1 X2 X3 : G, (k x x) = (τ (M.op X1 (M.op X2 (M.op X1 X3)))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq15836 X1 X2 X3 x
       have i₂ := eq68570 x
       grind)
    | exact superpose eq68570 eq15836
    | exact resolve eq15836 eq68570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15836
  have eq68930 : ∀ X0 : G, (k x x) ≠ X0 ∨ (k x x) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq68570 X0
       grind)
    | exact superpose eq68570 eq12
    | (have r₁ := eq12 (k x x) (k x x)
       have r₂ := eq68570 (k x x)
       grind)
    | exact resolve eq12 eq68570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68975 : ∀ X1 : G, (k x x) = (σ (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq16162 X1 (M.op x x) x
       have i₂ := eq68570 (M.op x x)
       grind)
    | exact superpose eq68570 eq16162
    | exact resolve eq16162 eq68570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16162
  have eq69003 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15893 X0 (τ (M.op X0 X0))
       have i₂ := eq68570 (τ (M.op X0 X0))
       grind)
    | exact superpose eq68570 eq15893
    | exact resolve eq15893 eq68570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15893
  have eq69025 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ x) (τ x)) := by
    intro X0
    first
    | (have i₁ := eq356 x x
       have i₂ := eq68570 X0
       grind)
    | exact superpose eq68570 eq356
    | exact resolve eq356 eq68570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq69787 : ∀ X0 X1 : G, (k X1 X1) = (k (τ x) (τ x)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38314 X0 X1
       have i₂ := eq69025 X0
       grind)
    | exact superpose eq69025 eq38314
    | (have j0 := eq38314 X0 X1
       grind)
    | exact resolve eq38314 eq69025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38314
  have eq71210 : (k x x) = (k (τ x) (τ x)) := by
    first
    | (have i₁ := eq69003 x
       have i₂ := eq69025 x
       grind)
    | exact superpose eq69025 eq69003
    | exact resolve eq69003 eq69025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69003
  have eq74856 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69025 X0
       have i₂ := eq71210
       grind)
    | exact superpose eq71210 eq69025
    | exact resolve eq69025 eq71210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69025
  have eq75087 : ∀ X0 X1 : G, (k x x) = (k X1 X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69787 X0 X1
       have i₂ := eq71210
       grind)
    | exact superpose eq71210 eq69787
    | (have j0 := eq69787 X0 X1
       grind)
    | exact resolve eq69787 eq71210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69787 eq71210
  have eq85063 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k x x) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq75087 X0 X1
       grind)
    | exact superpose eq75087 eq10
    | (have j1 := eq75087 X0 X1
       grind)
    | exact resolve eq10 eq75087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75087
  have eq85295 : ∀ X1 : G, (k x x) = X1 ∨ (k x x) = (k X1 X1) := by
    intro X1
    first
    | (have i₁ := eq85063 x X1
       have i₂ := eq74856 x
       grind)
    | exact superpose eq74856 eq85063
    | (have j0 := eq85063 x X1
       grind)
    | exact resolve eq85063 eq74856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74856 eq85063
  have eq85344 : ∀ X1 : G, (k x x) = (k X1 X1) := by
    intro X1
    first
    | (have j0 := eq85295 (k X1 X1)
       have j1 := eq68930 X1
       grind)
    | (have r₁ := eq85295 x
       have r₂ := eq68930 x
       grind)
    | (have r₁ := eq85295 (k x x)
       have r₂ := eq68930 (k x x)
       grind)
    | (have r₁ := eq85295 X1
       have r₂ := eq68930 (k X1 X1)
       grind)
    | exact resolve eq85295 eq68930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68930 eq85295
  have eq85468 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68570 X1
       have i₂ := eq85344 X0
       grind)
    | (have i₁ := eq68570 X0
       have i₂ := eq85344 x
       grind)
    | exact superpose eq85344 eq68570
    | exact resolve eq68570 eq85344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68570 eq85344
  have eq86195 : ∀ X0 X1 : G, (k X0 X0) = (M.op x (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq13015 X1 (M.op x (M.op X1 x))
       have i₂ := eq85468 X0 (M.op x (M.op X1 x))
       grind)
    | exact superpose eq85468 eq13015
    | exact resolve eq13015 eq85468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85468
  have eq87679 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (M.op x y)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58952 X1
       have i₂ := eq68975 X0
       grind)
    | exact superpose eq68975 eq58952
    | (have j0 := eq58952 X1
       grind)
    | exact resolve eq58952 eq68975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58952 eq68975
  have eq283482 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq15505
       have i₂ := eq15437
       grind)
    | exact superpose eq15437 eq15505
    | exact resolve eq15505 eq15437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15437 eq15505
  have eq283531 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq283482
  have eq283542 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13753
       have i₂ := eq283531
       grind)
    | exact superpose eq283531 eq13753
    | exact resolve eq13753 eq283531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13753
  have eq283585 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq283531
       grind)
    | exact superpose eq283531 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq283531
       grind)
    | exact resolve eq12 eq283531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283531
  have eq283607 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq283585
  have eq283608 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq283607
       have i₂ := eq12991
       grind)
    | exact superpose eq12991 eq283607
    | exact resolve eq283607 eq12991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283607
  have eq283649 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq283542
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq283542
    | exact resolve eq283542 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq283542
  have eq283650 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq283649
  have eq284178 : (σ y) ≠ (σ y) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq283650 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq283650
       grind)
    | exact resolve eq12 eq283650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283650
  have eq284200 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq284178
  have eq284202 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13447 eq284200
    | exact resolve eq284200 eq13447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284200
  have eq284204 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12997 eq284202
    | exact resolve eq284202 eq12997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12997 eq284202
  have eq291032 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq284204
       have i₂ := eq283608
       grind)
    | exact superpose eq283608 eq284204
    | exact resolve eq284204 eq283608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283608 eq284204
  have eq291093 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq291032
  have eq291102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq291093
       have i₂ := eq13446
       grind)
    | exact superpose eq13446 eq291093
    | exact resolve eq291093 eq13446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291093
  have eq291107 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq291102
       have r₂ := eq27
       grind)
    | exact resolve eq291102 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291102
  have eq291110 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq291107 eq27
    | exact resolve eq27 eq291107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq291111 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq291107 eq13447
    | exact resolve eq13447 eq291107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13447
  have eq291112 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq291107 eq13652
    | exact resolve eq13652 eq291107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13652 eq291107
  have eq291645 : (M.op (σ (M.op x y)) (σ y)) = (M.op x (M.op (σ (M.op x y)) x)) := by
    first
    | exact superpose eq291111 eq291112
    | exact resolve eq291112 eq291111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291112
  have eq291760 : (σ y) = (M.op x (M.op (σ (M.op x y)) x)) := by
    first
    | exact superpose eq291111 eq291645
    | exact resolve eq291645 eq291111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291645
  have eq291790 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq291760 eq13003
    | exact resolve eq13003 eq291760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13003
  have eq291794 : ∀ X0 : G, (σ y) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq291760 eq13013
    | exact resolve eq13013 eq291760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13013
  have eq291795 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq291760 eq13015
    | exact resolve eq13015 eq291760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13015
  have eq291800 : ∀ X0 : G, (σ (σ y)) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq291760 eq16821
    | exact resolve eq16821 eq291760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16821
  have eq291809 : ∀ X0 : G, (σ (σ (σ y))) = (σ (σ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq291760 eq18512
    | exact resolve eq18512 eq291760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18512
  have eq291841 : (k x x) = (τ (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq291760 eq68739
    | exact resolve eq68739 eq291760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68739 eq291760
  have eq291868 : (τ (σ y)) = (k x x) := by
    first
    | exact superpose eq291111 eq291841
    | exact resolve eq291841 eq291111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291111 eq291841
  have eq296510 : ∀ X1 : G, (σ (M.op x y)) ≠ (σ (σ (σ y))) ∨ (σ (M.op x y)) = (M.op X1 X1) := by
    intro X1
    first
    | (have i₁ := eq87679 x X1
       have i₂ := eq291809 x
       grind)
    | exact superpose eq291809 eq87679
    | (have j0 := eq87679 x X1
       grind)
    | exact resolve eq87679 eq291809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87679 eq291809
  have eq300654 : ∀ X0 : G, (σ y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq86195 X0 x
       have i₂ := eq291794 x
       grind)
    | exact superpose eq291794 eq86195
    | exact resolve eq86195 eq291794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86195
  have eq300924 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq291800 x
       have i₂ := eq291794 x
       grind)
    | exact superpose eq291794 eq291800
    | exact resolve eq291800 eq291794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291794 eq291800
  have eq301840 : y = (k x x) := by
    first
    | exact superpose eq39 eq291868
    | exact resolve eq291868 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq291868
  have eq308056 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) ≠ (σ (σ (σ y))) := by
    first
    | (have i₁ := eq296510 x
       have i₂ := eq291790 x
       grind)
    | exact superpose eq291790 eq296510
    | exact resolve eq296510 eq291790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291790 eq296510
  have eq311997 : y = (σ y) := by
    first
    | (have i₁ := eq301840
       have i₂ := eq300654 x
       grind)
    | exact superpose eq300654 eq301840
    | exact resolve eq301840 eq300654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300654 eq301840
  have eq316964 : (σ (M.op x y)) ≠ (σ (σ (σ y))) := by
    first
    | (have r₁ := eq308056
       have r₂ := eq291110
       grind)
    | exact resolve eq308056 eq291110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291110 eq308056
  have eq321881 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq311997 eq291795
    | exact resolve eq291795 eq311997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291795
  have eq321973 : y = (σ y) := by
    first
    | exact superpose eq311997 eq300924
    | exact resolve eq300924 eq311997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300924
  have eq326635 : (σ (M.op x y)) ≠ (σ (σ y)) := by
    first
    | exact superpose eq311997 eq316964
    | exact resolve eq316964 eq311997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311997 eq316964
  have eq329969 : x = y := by
    first
    | (have i₁ := eq12991
       have i₂ := eq321881 x
       grind)
    | exact superpose eq321881 eq12991
    | exact resolve eq12991 eq321881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12991 eq321881
  have eq333973 : (σ y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq326635
       have i₂ := eq321973
       grind)
    | exact superpose eq321973 eq326635
    | exact resolve eq326635 eq321973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321973 eq326635
  have eq341905 : (σ x) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq333973
       have i₂ := eq329969
       grind)
    | exact superpose eq329969 eq333973
    | exact resolve eq333973 eq329969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329969 eq333973
  have eq348725 : False := by grind
  exact eq348725

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_y_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq25 eq36
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq67 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X2))) X1) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    grind
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq240 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq248 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X1 X2
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1109 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 x X1 (M.op X0 (M.op X1 (M.op X0 x)))
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq67
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq1137 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1109 X0 X1
       have i₂ := eq248 X0 X0
       grind)
    | exact superpose eq248 eq1109
    | exact resolve eq1109 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1310 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X0
       have i₂ := eq56 X0 (σ X0)
       grind)
    | exact superpose eq56 eq96
    | exact resolve eq96 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1325 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (σ X0)
       have i₂ := eq96 X0 X0
       grind)
    | exact superpose eq96 eq56
    | (have j1 := eq96 X0 X0
       grind)
    | exact resolve eq56 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1343 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq96 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1344 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq1354 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1325 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1369 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1310 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1376 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1354 X0 X1
       have i₂ := eq248 X1 X1
       grind)
    | exact superpose eq248 eq1354
    | (have j0 := eq1354 X0 X1
       grind)
    | exact resolve eq1354 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1378 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1369 X0 X1
       have i₂ := eq248 X0 X0
       grind)
    | exact superpose eq248 eq1369
    | (have j0 := eq1369 X0 X1
       grind)
    | exact resolve eq1369 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1394 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1378 X0 X1
       have i₂ := eq248 X0 X0
       grind)
    | exact superpose eq248 eq1378
    | (have j0 := eq1378 X0 X1
       grind)
    | exact resolve eq1378 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq1378
  have eq5609 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1394 X0 (τ X1)
       grind)
    | exact superpose eq1394 eq35
    | (have j1 := eq1394 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq5640 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5609 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5609
    | (have j0 := eq5609 X0 X1
       grind)
    | exact resolve eq5609 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5609
  have eq5700 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5640 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5640
    | (have j0 := eq5640 X0 X1
       grind)
    | exact resolve eq5640 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5640
  have eq8244 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq5700 X0 x
       grind)
    | exact superpose eq5700 eq44
    | (have j1 := eq5700 X0 x
       grind)
    | exact resolve eq44 eq5700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9969 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1344 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1344
    | (have j0 := eq1344 (τ X0)
       grind)
    | exact resolve eq1344 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1344
  have eq9977 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9969 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9969
    | (have j0 := eq9969 X0
       grind)
    | exact resolve eq9969 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9969
  have eq9986 : ∀ X0 : G, (σ (τ X0)) = (M.op x (M.op (σ (τ X0)) (M.op x y))) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq9977 X0
       have i₂ := eq52 (σ (τ X0))
       grind)
    | exact superpose eq52 eq9977
    | (have j0 := eq9977 X0
       grind)
    | exact resolve eq9977 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9977
  have eq9991 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op x (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9986 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9986
    | (have j0 := eq9986 X0
       grind)
    | exact resolve eq9986 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9986
  have eq10201 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1376 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1376
    | (have j0 := eq1376 x X0
       grind)
    | exact resolve eq1376 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq10306 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10201 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10201
    | exact resolve eq10201 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10201
  have eq11002 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op x (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq10306 eq9991
    | (have j0 := eq9991 (σ x)
       grind)
    | exact resolve eq9991 eq10306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9991 eq10306
  have eq11014 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq11002
    | (have j0 := eq11002 X0
       grind)
    | exact resolve eq11002 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq11002
  have eq11015 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq11014 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11014
  have eq43889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43897 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq43889
    | exact resolve eq43889 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43889
  have eq43908 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq43897
       have r₂ := eq28
       grind)
    | exact resolve eq43897 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43897
  have eq43913 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq43908
  have eq43993 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq43913
    | exact resolve eq43913 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43913
  have eq44026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq43993 eq117
    | exact resolve eq117 eq43993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq43993
  have eq44042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq44026
  have eq44045 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq44042
       have r₂ := eq28
       grind)
    | exact resolve eq44042 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44042
  have eq44048 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq44045 eq14
    | exact resolve eq14 eq44045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44136 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq44045 eq44048
    | exact resolve eq44048 eq44045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44048
  have eq44359 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq44136
  have eq44458 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq44359 eq11015
    | exact resolve eq11015 eq44359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11015 eq44359
  have eq44489 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq44458
       have r₂ := eq44045
       grind)
    | exact resolve eq44458 eq44045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44458
  have eq44493 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  have eq44502 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq44489 eq411
    | exact resolve eq411 eq44489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq46164 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq44489
       have i₂ := eq44502 sF2 x
       grind)
    | exact superpose eq44502 eq44489
    | exact resolve eq44489 eq44502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44489
  have eq46246 : ∀ X0 : G, x ≠ (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    grind
  clear eq44502
  have eq46257 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq46164 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46164
  have eq46348 : x ≠ (σ x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq44045 eq46246
    | exact resolve eq46246 eq44045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44045 eq46246
  have eq46351 : x ≠ (σ x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq46348
  have eq46395 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (σ x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq46257 eq8244
    | (have j0 := eq8244 y
       grind)
    | exact resolve eq8244 eq46257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8244
  have eq46457 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq46395
       have r₂ := eq46351
       grind)
    | exact resolve eq46395 eq46351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46395
  have eq46587 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq46457 eq44493
    | exact resolve eq44493 eq46457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44493 eq46457
  have eq46620 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq46587
  have eq46731 : (σ x) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq46620 eq46257
    | exact resolve eq46257 eq46620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46257 eq46620
  have eq46809 : x = (M.op y y) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) := by grind
  clear eq46731
  have eq46843 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq56 y X0
       have i₂ := eq46809
       grind)
    | exact superpose eq46809 eq56
    | exact resolve eq56 eq46809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47853 : x = (M.op y x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq46809
       have i₂ := eq46843 y
       grind)
    | exact superpose eq46843 eq46809
    | exact resolve eq46809 eq46843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46809 eq46843
  have eq47895 : x = (M.op y x) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq47853
  have eq47986 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op X0 x)) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq47895
       grind)
    | exact superpose eq47895 eq14
    | exact resolve eq14 eq47895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48082 : (M.op y x) = (M.op y y) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq47986 y
       have i₂ := eq47895
       grind)
    | exact superpose eq47895 eq47986
    | exact resolve eq47986 eq47895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47986
  have eq48316 : (M.op y x) = (M.op y y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq48082
  have eq48377 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48316
       have i₂ := eq240 y X0
       grind)
    | (have i₁ := eq48316
       have i₂ := eq240 X0 y
       grind)
    | exact superpose eq240 eq48316
    | exact resolve eq48316 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq48316
  have eq48757 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq47895
       have i₂ := eq48377 X0
       grind)
    | exact superpose eq48377 eq47895
    | exact resolve eq47895 eq48377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47895 eq48377
  have eq48783 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have j0 := eq48757 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48757
  have eq48932 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    grind
  have eq48983 : ∀ X1 : G, x = (k X1 X1) ∨ x = X1 ∨ (σ x) = (σ (σ x)) := by
    intro X1
    first
    | (have i₁ := eq5700 x X1
       have i₂ := eq48783 x
       grind)
    | exact superpose eq48783 eq5700
    | exact resolve eq5700 eq48783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5700
  have eq50333 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq48932 x
       grind)
    | exact superpose eq48932 eq44
    | exact resolve eq44 eq48932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq48932
  have eq54007 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq50333
       have i₂ := eq48783 x
       grind)
    | exact superpose eq48783 eq50333
    | exact resolve eq50333 eq48783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48783 eq50333
  have eq54101 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq54007
  have eq54157 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq54101
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq54101
    | exact resolve eq54101 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54101
  have eq54218 : x = (σ x) ∨ x = (σ x) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq54157 eq48983
    | (have j0 := eq48983 (σ x)
       grind)
    | exact resolve eq48983 eq54157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48983 eq54157
  have eq54233 : (σ x) = (σ (σ x)) ∨ x = (σ x) := by grind
  clear eq54218
  have eq54269 : (σ x) = (τ (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq54233 eq16
    | exact resolve eq16 eq54233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54233
  have eq54350 : x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq54269
    | exact resolve eq54269 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq54269
  have eq54351 : x = (σ x) := by grind
  clear eq54350
  have eq54356 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq54351 eq27
    | exact resolve eq27 eq54351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq54446 : x ≠ x ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq54351 eq46351
    | (have r₁ := eq46351
       have r₂ := eq54351
       grind)
    | exact resolve eq46351 eq54351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46351
  have eq54456 : x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq54446
  have eq56534 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq56 y X0
       have i₂ := eq54456
       grind)
    | exact superpose eq54456 eq56
    | exact resolve eq56 eq54456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq66055 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq54456
       have i₂ := eq56534 y
       grind)
    | exact superpose eq56534 eq54456
    | exact resolve eq54456 eq56534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54456 eq56534
  have eq66115 : x = (M.op y x) := by grind
  clear eq66055
  have eq66280 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq66115
       grind)
    | exact superpose eq66115 eq14
    | exact resolve eq14 eq66115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66763 : (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq66280 y
       have i₂ := eq66115
       grind)
    | exact superpose eq66115 eq66280
    | exact resolve eq66280 eq66115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66280
  have eq67084 : x = (M.op y y) := by
    first
    | (have i₁ := eq66763
       have i₂ := eq66115
       grind)
    | exact superpose eq66115 eq66763
    | exact resolve eq66763 eq66115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66115 eq66763
  have eq67160 : (M.op x y) = (k x y) := by grind
  have eq67177 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1137 y x
       have i₂ := eq67084
       grind)
    | exact superpose eq67084 eq1137
    | exact resolve eq1137 eq67084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq67084
  have eq67263 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq67160
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67160
    | exact resolve eq67160 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq67160
  have eq68030 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq67263
       grind)
    | exact superpose eq67263 eq45
    | exact resolve eq45 eq67263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq67263
  have eq68063 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq54351 eq68030
    | exact resolve eq68030 eq54351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54351 eq68030
  have eq68079 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq21 eq68063
    | exact resolve eq68063 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq68063
  have eq70717 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq68079
       have i₂ := eq67177 sF3
       grind)
    | exact superpose eq67177 eq68079
    | exact resolve eq68079 eq67177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67177 eq68079
  have eq70718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54356 eq70717
    | exact resolve eq70717 eq54356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54356 eq70717
  have eq70842 : False := by grind
  exact eq70842
