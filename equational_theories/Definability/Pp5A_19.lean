import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_y_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq179 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (σ x) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq39
    | exact resolve eq39 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq186 : (σ x) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq181
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq181
    | exact resolve eq181 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq193 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 y
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq198 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq204 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq152
    | exact resolve eq152 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq174
  have eq289 : y = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq31 eq268
    | exact resolve eq268 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq722 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq723 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq722
       grind)
    | exact superpose eq722 eq40
    | exact resolve eq40 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1101
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1101
    | exact resolve eq1101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1102
    | exact resolve eq1102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1192 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq178 eq204
    | exact resolve eq204 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1213 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq1192 X0
       grind)
    | exact superpose eq1192 eq16
    | exact resolve eq16 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1268 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq178 eq1213
    | exact resolve eq1213 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1272 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq179 eq1213
    | exact resolve eq1213 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1213
  have eq2103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1104 eq723
    | exact resolve eq723 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq2112 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2103
       have r₂ := eq27
       grind)
    | exact resolve eq2103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq2120 : y = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2112 eq289
    | exact resolve eq289 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112
  have eq2141 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq2120
    | exact resolve eq2120 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq2145 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq2141
       have r₂ := eq13 x y
       grind)
    | exact resolve eq2141 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141
  have eq2147 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq722
       have i₂ := eq2145
       grind)
    | exact superpose eq2145 eq722
    | exact resolve eq722 eq2145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq2148 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq2145
       grind)
    | exact superpose eq2145 eq35
    | exact resolve eq35 eq2145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2145
  have eq2151 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2147
  have eq2156 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2148
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2148
    | exact resolve eq2148 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq2162 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2156 eq723
    | exact resolve eq723 eq2156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq2156
  have eq2167 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2162
  have eq2246 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1192 y
       have i₂ := eq2151
       grind)
    | exact superpose eq2151 eq1192
    | exact resolve eq1192 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq2262 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2246
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2246
    | exact resolve eq2246 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246
  have eq2263 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2262
  have eq2274 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2263 eq198
    | exact resolve eq198 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2291 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2263 eq1272
    | exact resolve eq1272 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2304 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2291 eq2274
    | exact resolve eq2274 eq2291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274
  have eq2310 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2304
    | exact resolve eq2304 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304
  have eq2311 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2263 eq2310
    | exact resolve eq2310 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq2313 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2311 eq31
    | exact resolve eq31 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2330 : y = (k (τ (M.op (σ x) (σ x))) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2311 eq289
    | exact resolve eq289 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq2311
  have eq2369 : y = (k (τ (σ x)) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2291 eq2330
    | exact resolve eq2330 eq2291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291 eq2330
  have eq2383 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2313
    | exact resolve eq2313 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2313
  have eq2388 : y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2369
    | exact resolve eq2369 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2369
  have eq2391 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2383 eq2388
    | exact resolve eq2388 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388
  have eq2394 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq2383
       grind)
    | exact superpose eq2383 eq24
    | exact resolve eq24 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2436 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq2394
    | exact resolve eq2394 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394
  have eq2509 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq761 x x
       have i₂ := eq2391
       grind)
    | exact superpose eq2391 eq761
    | (have j0 := eq761 x x
       grind)
    | (have r₁ := eq761 x x
       have r₂ := eq2391
       grind)
    | exact resolve eq761 eq2391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq2510 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2509
  have eq2511 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2510
  have eq3367 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2167 eq1192
    | exact resolve eq1192 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192 eq2167
  have eq3386 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3367
    | exact resolve eq3367 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367
  have eq3387 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3386
  have eq3394 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3387 eq27
    | exact resolve eq27 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387
  have eq3426 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2436 eq3394
    | (have r₁ := eq3394
       have r₂ := eq2436
       grind)
    | exact resolve eq3394 eq2436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3394
  have eq3427 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3426
  have eq3428 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3427
  have eq3429 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2263 eq3428
    | exact resolve eq3428 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263 eq3428
  have eq3430 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3429
  have eq3433 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3430 eq27
    | exact resolve eq27 eq3430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3436 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3430 eq198
    | exact resolve eq198 eq3430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq3454 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3430 eq1272
    | exact resolve eq1272 eq3430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq3469 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3454 eq3436
    | exact resolve eq3436 eq3454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3436 eq3454
  have eq3475 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3469
    | exact resolve eq3469 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3469
  have eq3476 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3430 eq3475
    | exact resolve eq3475 eq3430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3430 eq3475
  have eq3477 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2436 eq3433
    | exact resolve eq3433 eq2436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436 eq3433
  have eq3478 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3477
  have eq3479 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq3478
       have r₂ := eq3476
       grind)
    | exact resolve eq3478 eq3476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476 eq3478
  have eq3575 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq3479
       grind)
    | exact superpose eq3479 eq18
    | exact resolve eq18 eq3479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3591 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1268
       have i₂ := eq3479
       grind)
    | exact superpose eq3479 eq1268
    | exact resolve eq1268 eq3479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq3981 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq3591 eq193
    | exact resolve eq193 eq3591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq3591
  have eq4007 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3575 eq3981
    | exact resolve eq3981 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3575 eq3981
  have eq4049 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq4007
  have eq4050 : x = y := by
    first
    | (have r₁ := eq4049
       have r₂ := eq3479
       grind)
    | exact resolve eq4049 eq3479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479 eq4049
  have eq4060 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4050
       grind)
    | exact superpose eq4050 eq18
    | exact resolve eq18 eq4050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4061 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4050
       grind)
    | exact superpose eq4050 eq24
    | exact resolve eq24 eq4050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq4105 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4061
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4061
    | exact resolve eq4061 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4061
  have eq4107 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4105 eq26
    | exact resolve eq26 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4105
  have eq4182 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2511
       have i₂ := eq4060
       grind)
    | exact superpose eq4060 eq2511
    | exact resolve eq2511 eq4060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq4183 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq186
       have i₂ := eq4060
       grind)
    | exact superpose eq4060 eq186
    | exact resolve eq186 eq4060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq4060
  have eq4212 : x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4182
  have eq4216 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq4183
    | exact resolve eq4183 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4183
  have eq4217 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4212
       have i₂ := eq4050
       grind)
    | exact superpose eq4050 eq4212
    | exact resolve eq4212 eq4050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4050 eq4212
  have eq4218 : x = (M.op x y) := by grind
  clear eq4217
  have eq4223 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4218
       grind)
    | exact superpose eq4218 eq22
    | exact resolve eq22 eq4218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4218
  have eq4260 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4223 eq20
    | exact resolve eq20 eq4223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4223
  have eq4458 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4216 eq761
    | (have j0 := eq761 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq761 eq4216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq4216
  have eq4459 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq4458
       have r₂ := eq4260
       grind)
    | exact resolve eq4458 eq4260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4458
  have eq4464 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4260 eq4459
    | exact resolve eq4459 eq4260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4459
  have eq4467 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4107 eq4464
    | exact resolve eq4464 eq4107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4464
  have eq4470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4107 eq4467
    | exact resolve eq4467 eq4107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4107 eq4467
  have eq4472 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4470
       have r₂ := eq27
       grind)
    | exact resolve eq4470 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470
  have eq4476 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4472 eq27
    | exact resolve eq27 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4472
  have eq4518 : False := by grind
  exact eq4518

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_y_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq179 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (σ x) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq39
    | exact resolve eq39 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq186 : (σ x) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq181
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq181
    | exact resolve eq181 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq193 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 y
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq198 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq204 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq152
    | exact resolve eq152 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq174
  have eq289 : y = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq31 eq268
    | exact resolve eq268 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq722 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq723 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq722
       grind)
    | exact superpose eq722 eq40
    | exact resolve eq40 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1099
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1099
    | exact resolve eq1099 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1100
    | exact resolve eq1100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1188 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq178 eq204
    | exact resolve eq204 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1209 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq1188 X0
       grind)
    | exact superpose eq1188 eq16
    | exact resolve eq16 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq178 eq1209
    | exact resolve eq1209 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1266 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq179 eq1209
    | exact resolve eq1209 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1209
  have eq2086 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1102 eq723
    | exact resolve eq723 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq2095 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2086
       have r₂ := eq27
       grind)
    | exact resolve eq2086 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086
  have eq2103 : y = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2095 eq289
    | exact resolve eq289 eq2095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095
  have eq2124 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq2103
    | exact resolve eq2103 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq2128 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq2124
       have r₂ := eq13 x y
       grind)
    | exact resolve eq2124 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq2130 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq722
       have i₂ := eq2128
       grind)
    | exact superpose eq2128 eq722
    | exact resolve eq722 eq2128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq2131 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq2128
       grind)
    | exact superpose eq2128 eq35
    | exact resolve eq35 eq2128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2128
  have eq2134 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2130
  have eq2139 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2131
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2131
    | exact resolve eq2131 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq2145 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2139 eq723
    | exact resolve eq723 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq2139
  have eq2150 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2145
  have eq2229 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1188 y
       have i₂ := eq2134
       grind)
    | exact superpose eq2134 eq1188
    | exact resolve eq1188 eq2134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134
  have eq2245 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2229
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2229
    | exact resolve eq2229 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229
  have eq2246 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2245
  have eq2257 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2246 eq198
    | exact resolve eq198 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2274 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2246 eq1266
    | exact resolve eq1266 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2287 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2274 eq2257
    | exact resolve eq2257 eq2274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq2293 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2287
    | exact resolve eq2287 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2287
  have eq2294 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2246 eq2293
    | exact resolve eq2293 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2293
  have eq2296 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2294 eq31
    | exact resolve eq31 eq2294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2313 : y = (k (τ (M.op (σ x) (σ x))) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2294 eq289
    | exact resolve eq289 eq2294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq2294
  have eq2352 : y = (k (τ (σ x)) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2274 eq2313
    | exact resolve eq2313 eq2274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274 eq2313
  have eq2366 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2296
    | exact resolve eq2296 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq2371 : y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2352
    | exact resolve eq2352 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2352
  have eq2374 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2366 eq2371
    | exact resolve eq2371 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq2377 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq2366
       grind)
    | exact superpose eq2366 eq24
    | exact resolve eq24 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2419 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq2377
    | exact resolve eq2377 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq2492 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq761 x x
       have i₂ := eq2374
       grind)
    | exact superpose eq2374 eq761
    | (have j0 := eq761 x x
       grind)
    | (have r₁ := eq761 x x
       have r₂ := eq2374
       grind)
    | exact resolve eq761 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq2493 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2492
  have eq2494 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2493
  have eq3341 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2150 eq1188
    | exact resolve eq1188 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188 eq2150
  have eq3360 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3341
    | exact resolve eq3341 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341
  have eq3361 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3360
  have eq3368 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3361 eq27
    | exact resolve eq27 eq3361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3361
  have eq3400 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2419 eq3368
    | (have r₁ := eq3368
       have r₂ := eq2419
       grind)
    | exact resolve eq3368 eq2419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3368
  have eq3401 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3400
  have eq3402 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3401
  have eq3403 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2246 eq3402
    | exact resolve eq3402 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246 eq3402
  have eq3404 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3403
  have eq3407 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3404 eq27
    | exact resolve eq27 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3410 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3404 eq198
    | exact resolve eq198 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq3428 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3404 eq1266
    | exact resolve eq1266 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq3443 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3428 eq3410
    | exact resolve eq3410 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410 eq3428
  have eq3449 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3443
    | exact resolve eq3443 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq3450 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3404 eq3449
    | exact resolve eq3449 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404 eq3449
  have eq3451 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2419 eq3407
    | exact resolve eq3407 eq2419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419 eq3407
  have eq3452 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3451
  have eq3453 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq3452
       have r₂ := eq3450
       grind)
    | exact resolve eq3452 eq3450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3450 eq3452
  have eq3549 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq3453
       grind)
    | exact superpose eq3453 eq18
    | exact resolve eq18 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3565 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1262
       have i₂ := eq3453
       grind)
    | exact superpose eq3453 eq1262
    | exact resolve eq1262 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq3955 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq3565 eq193
    | exact resolve eq193 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq3565
  have eq3981 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3549 eq3955
    | exact resolve eq3955 eq3549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3549 eq3955
  have eq4023 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq3981
  have eq4024 : x = y := by
    first
    | (have r₁ := eq4023
       have r₂ := eq3453
       grind)
    | exact resolve eq4023 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3453 eq4023
  have eq4034 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4024
       grind)
    | exact superpose eq4024 eq18
    | exact resolve eq18 eq4024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4035 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4024
       grind)
    | exact superpose eq4024 eq24
    | exact resolve eq24 eq4024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq4079 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4035
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4035
    | exact resolve eq4035 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035
  have eq4081 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4079 eq26
    | exact resolve eq26 eq4079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4079
  have eq4156 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2494
       have i₂ := eq4034
       grind)
    | exact superpose eq4034 eq2494
    | exact resolve eq2494 eq4034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq4157 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq186
       have i₂ := eq4034
       grind)
    | exact superpose eq4034 eq186
    | exact resolve eq186 eq4034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq4034
  have eq4186 : x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4156
  have eq4190 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq4157
    | exact resolve eq4157 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4157
  have eq4191 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4186
       have i₂ := eq4024
       grind)
    | exact superpose eq4024 eq4186
    | exact resolve eq4186 eq4024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4024 eq4186
  have eq4192 : x = (M.op x y) := by grind
  clear eq4191
  have eq4197 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4192
       grind)
    | exact superpose eq4192 eq22
    | exact resolve eq22 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4192
  have eq4234 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4197 eq20
    | exact resolve eq20 eq4197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4197
  have eq4432 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4190 eq761
    | (have j0 := eq761 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq761 eq4190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq4190
  have eq4433 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq4432
       have r₂ := eq4234
       grind)
    | exact resolve eq4432 eq4234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4432
  have eq4438 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4234 eq4433
    | exact resolve eq4433 eq4234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4433
  have eq4441 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4081 eq4438
    | exact resolve eq4438 eq4081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4438
  have eq4444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4081 eq4441
    | exact resolve eq4441 eq4081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4081 eq4441
  have eq4446 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4444
       have r₂ := eq27
       grind)
    | exact resolve eq4444 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4444
  have eq4450 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4446 eq27
    | exact resolve eq27 eq4446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4446
  have eq4492 : False := by grind
  exact eq4492

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq123 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq155 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq176 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq155
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq155
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq178 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq176
  have eq247 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq247
  have eq515 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq523 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq515 X0
       grind)
    | exact superpose eq515 eq14
    | exact resolve eq14 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq515 (σ X0)
       have i₂ := eq93 X0 X0
       grind)
    | exact superpose eq93 eq515
    | (have j1 := eq93 X0 X0
       grind)
    | exact resolve eq515 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq711 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq704 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq871 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq523
    | exact resolve eq523 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq523
    | exact resolve eq523 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq523
  have eq29235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq29235
    | exact resolve eq29235 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29235
  have eq29256 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq29245
       have r₂ := eq28
       grind)
    | exact resolve eq29245 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29245
  have eq29258 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29256 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq29256
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq29256
       grind)
    | exact resolve eq12 eq29256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29256
  have eq29308 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq29258
  have eq29309 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq29308
  have eq29763 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29309 eq60
    | exact resolve eq60 eq29309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq29309
  have eq29796 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq29763
    | exact resolve eq29763 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29763
  have eq29800 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq29796
       have r₂ := eq12 x y
       grind)
    | exact resolve eq29796 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29796
  have eq29807 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq29800
  have eq29860 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq29807
    | exact resolve eq29807 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29807
  have eq30436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29860 eq114
    | exact resolve eq114 eq29860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq29860
  have eq30457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq30436
  have eq30461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq30457
       have r₂ := eq12 x y
       grind)
    | exact resolve eq30457 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30457
  have eq30464 : x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq30461
       have r₂ := eq28
       grind)
    | exact resolve eq30461 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30461
  have eq30476 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq30464
       grind)
    | exact superpose eq30464 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq30464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30464
  have eq30487 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq30476
  have eq30498 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30487
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30487
    | exact resolve eq30487 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30487
  have eq30611 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq30498
       grind)
    | exact superpose eq30498 eq14
    | exact resolve eq14 eq30498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30657 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq871 y x
       have i₂ := eq30498
       grind)
    | exact superpose eq30498 eq871
    | exact resolve eq871 eq30498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30686 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq30611 X0
       have i₂ := eq871 y X0
       grind)
    | exact superpose eq871 eq30611
    | exact resolve eq30611 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30611
  have eq30961 : x ≠ y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq30657
  have eq32505 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30686 x
       have i₂ := eq30498
       grind)
    | exact superpose eq30498 eq30686
    | exact resolve eq30686 eq30498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30686
  have eq32593 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq32505
  have eq32672 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq871 y y
       have i₂ := eq32593
       grind)
    | exact superpose eq32593 eq871
    | exact resolve eq871 eq32593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871 eq32593
  have eq32675 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq32672
  have eq32750 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30498
       have i₂ := eq32675
       grind)
    | exact superpose eq32675 eq30498
    | exact resolve eq30498 eq32675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30498 eq32675
  have eq32803 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq32750
  have eq32806 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq32803
       have r₂ := eq30961
       grind)
    | exact resolve eq32803 eq30961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30961 eq32803
  have eq32813 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq32806
       grind)
    | exact superpose eq32806 eq109
    | exact resolve eq109 eq32806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq32815 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq515 y
       have i₂ := eq32806
       grind)
    | exact superpose eq32806 eq515
    | exact resolve eq515 eq32806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32806
  have eq32874 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32815
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32815
    | exact resolve eq32815 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32815
  have eq32876 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32813
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32813
    | exact resolve eq32813 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32813
  have eq32877 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32874 eq21
    | exact resolve eq21 eq32874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32887 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32874 eq123
    | exact resolve eq123 eq32874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq32986 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq32874
  have eq33042 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq32887 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq32887
    | exact resolve eq32887 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq32887
  have eq33050 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32877
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32877
    | exact resolve eq32877 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32877
  have eq33119 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33050 eq41
    | exact resolve eq41 eq33050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq33279 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq42 eq33119
    | exact resolve eq33119 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq33119
  have eq36965 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq32876
       have r₂ := eq32986
       grind)
    | exact resolve eq32876 eq32986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32876 eq32986
  have eq36975 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36965 eq87
    | exact resolve eq87 eq36965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq36989 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36965 eq33042
    | exact resolve eq33042 eq36965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33042 eq36965
  have eq37013 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq36989
  have eq37029 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq36975
    | exact resolve eq36975 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36975
  have eq51380 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq439 X0
       have i₂ := eq515 (σ X0)
       grind)
    | exact superpose eq515 eq439
    | exact resolve eq439 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq515
  have eq51381 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51380 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq51380
    | exact resolve eq51380 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51380
  have eq51796 : (σ (M.op x y)) = (σ (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33279 (τ (M.op (σ sF0) (σ sF0)))
       have i₂ := eq51381 sF0
       grind)
    | exact superpose eq51381 eq33279
    | exact resolve eq33279 eq51381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33279 eq51381
  have eq51805 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51796
       have i₂ := eq35 (M.op (σ sF0) (σ sF0)) y
       grind)
    | exact superpose eq35 eq51796
    | exact resolve eq51796 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq51796
  have eq51889 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51805
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq51805
    | exact resolve eq51805 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51805
  have eq51965 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq51889
    | exact resolve eq51889 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51889
  have eq52155 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq711 y
       have i₂ := eq37029
       grind)
    | exact superpose eq37029 eq711
    | (have j0 := eq711 y
       grind)
    | exact resolve eq711 eq37029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq37029
  have eq52389 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52155
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq52155
    | exact resolve eq52155 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52155
  have eq52417 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52389
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52389
    | exact resolve eq52389 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52389
  have eq52435 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq52417
    | exact resolve eq52417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52417
  have eq52442 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52435
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq52435
    | exact resolve eq52435 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52435
  have eq52451 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33050 eq52442
    | exact resolve eq52442 eq33050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33050 eq52442
  have eq52522 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq52451
  have eq52550 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq52522
       have r₂ := eq28
       grind)
    | exact resolve eq52522 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52522
  have eq52566 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52550 eq51965
    | exact resolve eq51965 eq52550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51965 eq52550
  have eq52631 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq52566
  have eq52689 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52631 eq37013
    | exact resolve eq37013 eq52631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37013 eq52631
  have eq52709 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq52689
  have eq53070 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52709 eq29
    | exact resolve eq29 eq52709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52709
  have eq53294 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq53070
    | exact resolve eq53070 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq53070
  have eq53295 : x = (M.op x y) := by grind
  clear eq53294
  have eq53297 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq53295 eq21
    | exact resolve eq21 eq53295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq53395 : x = (M.op x x) := by
    first
    | exact superpose eq53295 eq873
    | exact resolve eq873 eq53295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq53489 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53297
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53297
    | exact resolve eq53297 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53297
  have eq53501 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq53489 eq27
    | exact resolve eq27 eq53489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq53705 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq53395
       grind)
    | exact superpose eq53395 eq51
    | exact resolve eq51 eq53395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53731 : (k x x) = (M.op x x) := by grind
  have eq53821 : x = (k x x) := by
    first
    | (have i₁ := eq53731
       have i₂ := eq53395
       grind)
    | exact superpose eq53395 eq53731
    | exact resolve eq53731 eq53395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53731
  have eq53845 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq53295 eq53705
    | exact resolve eq53705 eq53295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53705
  have eq53873 : y = (M.op x y) := by
    first
    | (have i₁ := eq53845
       have i₂ := eq53395
       grind)
    | exact superpose eq53395 eq53845
    | exact resolve eq53845 eq53395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53395 eq53845
  have eq53890 : y = (M.op x y) := by
    first
    | (have i₁ := eq53873
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53873
    | exact resolve eq53873 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq53873
  have eq53897 : x = y := by
    first
    | exact superpose eq53295 eq53890
    | exact resolve eq53890 eq53295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53890
  have eq53911 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq53897
       grind)
    | exact superpose eq53897 eq25
    | exact resolve eq25 eq53897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq53897
  have eq54170 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq53911
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53911
    | exact resolve eq53911 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53911
  have eq54246 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq53489 eq54170
    | exact resolve eq54170 eq53489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54170
  have eq54610 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq54246 eq53501
    | exact resolve eq53501 eq54246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53501 eq54246
  have eq54805 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54610 eq178
    | exact resolve eq178 eq54610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq54610
  have eq54882 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq54805
       have r₂ := eq28
       grind)
    | exact resolve eq54805 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54805
  have eq54883 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq53295 eq54882
    | exact resolve eq54882 eq53295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53295 eq54882
  have eq54884 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq54883
       have i₂ := eq53821
       grind)
    | exact superpose eq53821 eq54883
    | exact resolve eq54883 eq53821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53821 eq54883
  have eq54886 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54884 eq15
    | exact resolve eq15 eq54884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54884
  have eq54988 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54886
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq54886
    | exact resolve eq54886 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54886
  have eq55023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53489 eq54988
    | exact resolve eq54988 eq53489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53489 eq54988
  have eq55047 : False := by grind
  exact eq55047

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq183 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq188 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq180 eq183
    | exact resolve eq183 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq183
  have eq550 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq16
    | exact resolve eq16 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq555 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq185 eq188
    | exact resolve eq188 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq188
  have eq558 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq555 eq16
    | exact resolve eq16 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq564 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq550 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq550
    | exact resolve eq550 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq574 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq558 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq558
    | exact resolve eq558 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq619 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq681 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq767 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq618
       grind)
    | exact superpose eq618 eq40
    | exact resolve eq40 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq768 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq767
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq767
    | exact resolve eq767 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq767
  have eq770 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq768
    | exact resolve eq768 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq824 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq191
    | exact resolve eq191 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq844 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq824 X0
       grind)
    | exact superpose eq824 eq16
    | exact resolve eq16 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq824 X0
       grind)
    | exact superpose eq824 eq16
    | exact resolve eq16 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq882 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq844
    | exact resolve eq844 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq844
    | exact resolve eq844 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq890 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq844
    | exact resolve eq844 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1083 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq886 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq886
       grind)
    | exact resolve eq12 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq1090 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq1083
  have eq1096 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq890 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq890
       grind)
    | exact resolve eq12 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq1103 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq1096
  have eq1281 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1090 eq35
    | exact resolve eq35 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1090
  have eq1284 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq1281
    | exact resolve eq1281 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1286 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1103 eq90
    | exact resolve eq90 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq770 eq619
    | exact resolve eq619 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq1945 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1934
       have r₂ := eq27
       grind)
    | exact resolve eq1934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934
  have eq1967 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1945 eq13
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1945
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1945
       grind)
    | exact resolve eq13 eq1945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq1968 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq2000 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1968 eq107
    | exact resolve eq107 eq1968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968
  have eq2010 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq2000
    | exact resolve eq2000 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq2022 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq682 y
       grind)
    | (have r₁ := eq2010
       have r₂ := eq682 y
       grind)
    | exact resolve eq2010 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2043 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq845 y X0
       have i₂ := eq2022
       grind)
    | exact superpose eq2022 eq845
    | exact resolve eq845 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq2044 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq844 y X0
       have i₂ := eq2022
       grind)
    | exact superpose eq2022 eq844
    | exact resolve eq844 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq2022
  have eq2049 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2043 X0
       have i₂ := eq564 X0
       grind)
    | exact superpose eq564 eq2043
    | exact resolve eq2043 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2764 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2044 X0
       have i₂ := eq2049 X0
       grind)
    | exact superpose eq2049 eq2044
    | exact resolve eq2044 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044
  have eq2797 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2764 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764
  have eq2864 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2049 X0
       have i₂ := eq2797 X0
       grind)
    | exact superpose eq2797 eq2049
    | exact resolve eq2049 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049 eq2797
  have eq2903 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2864 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864
  have eq3001 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2903 x
       grind)
    | exact superpose eq2903 eq18
    | (have j1 := eq2903 x
       grind)
    | exact resolve eq18 eq2903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2903
  have eq3031 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3001
  have eq3064 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3031 eq1286
    | exact resolve eq1286 eq3031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286 eq3031
  have eq3066 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq3064
    | exact resolve eq3064 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3064
  have eq3500 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3066 eq13
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq3066
       grind)
    | exact resolve eq13 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3066
  have eq3516 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3500 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3500
  have eq3579 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3516 eq90
    | exact resolve eq90 eq3516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3516
  have eq3595 : y = (k x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq3579
    | exact resolve eq3579 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3596 : y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq3595
  have eq3607 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq618
       have i₂ := eq3596
       grind)
    | exact superpose eq3596 eq618
    | exact resolve eq618 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq3596
  have eq3614 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq3607
  have eq3637 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq3614
       grind)
    | exact superpose eq3614 eq16
    | exact resolve eq16 eq3614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3638 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq3614
       grind)
    | exact superpose eq3614 eq16
    | exact resolve eq16 eq3614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3614
  have eq3660 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3637 X0
       have i₂ := eq564 X0
       grind)
    | exact superpose eq564 eq3637
    | exact resolve eq3637 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq3637
  have eq4220 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3638 X0
       have i₂ := eq3660 X0
       grind)
    | exact superpose eq3660 eq3638
    | exact resolve eq3638 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq4269 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4220
  have eq4355 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3660 X0
       have i₂ := eq4269 X0
       grind)
    | exact superpose eq4269 eq3660
    | exact resolve eq3660 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3660 eq4269
  have eq4399 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4355 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4355
  have eq4509 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4399 x
       grind)
    | exact superpose eq4399 eq18
    | (have j1 := eq4399 x
       grind)
    | exact resolve eq18 eq4399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4399
  have eq4551 : y = (M.op x y) := by grind
  clear eq4509
  have eq4564 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4551
       grind)
    | exact superpose eq4551 eq24
    | exact resolve eq24 eq4551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq4594 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4564 eq20
    | exact resolve eq20 eq4564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4564
  have eq4641 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4594 eq1284
    | exact resolve eq1284 eq4594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq5626 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4641 eq619
    | exact resolve eq619 eq4641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq4641
  have eq5635 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq5626
  have eq7259 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5635 eq13
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq5635
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq5635
       grind)
    | exact resolve eq13 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq7276 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq7259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7259
  have eq7316 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7276 eq107
    | exact resolve eq107 eq7276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq7276
  have eq7324 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31 eq7316
    | exact resolve eq7316 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7316
  have eq7338 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7324
       have i₂ := eq4551
       grind)
    | exact superpose eq4551 eq7324
    | exact resolve eq7324 eq4551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4551 eq7324
  have eq7349 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq682 (M.op x y)
       grind)
    | (have r₁ := eq7338
       have r₂ := eq682 (M.op x y)
       grind)
    | exact resolve eq7338 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq7338
  have eq7371 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7349 eq13
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq7349
       grind)
    | exact resolve eq13 eq7349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7372 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7349 eq16
    | exact resolve eq16 eq7349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7373 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7349 eq16
    | exact resolve eq16 eq7349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7349
  have eq7388 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7371
  have eq7395 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7372 x
       have i₂ := eq882 sF0 x
       grind)
    | exact superpose eq882 eq7372
    | exact resolve eq7372 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq7372
  have eq7423 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7388 eq37
    | exact resolve eq37 eq7388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq7388
  have eq7432 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq7423
    | exact resolve eq7423 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7423
  have eq7445 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4594 eq7432
    | exact resolve eq7432 eq4594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7432
  have eq7475 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7445 eq680
    | (have j0 := eq680 (σ y) (σ y)
       grind)
    | (have r₁ := eq680 (σ y) (σ y)
       have r₂ := eq7445
       grind)
    | exact resolve eq680 eq7445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq7445
  have eq7476 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7475
  have eq7477 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7476
  have eq7601 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7477 eq16
    | exact resolve eq16 eq7477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7623 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq574 eq7601
    | exact resolve eq7601 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq7601
  have eq7926 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7395 eq7373
    | exact resolve eq7373 eq7395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7373 eq7395
  have eq7974 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7926
  have eq8035 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f8035_14 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f8035_22 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f8035_23 : X1 ≠ (M.op (M.op (M.op (M.op x y) X1) X0) X1) := by grind
    have f8035_24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f8035_25 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f8035_14 X0
         grind)
      | (have r₁ := f8035_14 X0
         have r₂ := f8035_24
         grind)
      | exact resolve f8035_14 f8035_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8035_34 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X1) X0) X1) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f8035_22 X1 (M.op x y) X0
         have i₂ := f8035_25 X0
         grind)
      | exact superpose f8035_25 f8035_22
      | exact resolve f8035_22 f8035_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8035_37 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f8035_34 X0 X1
         have i₂ := f8035_25 X1
         grind)
      | exact superpose f8035_25 f8035_34
      | exact resolve f8035_34 f8035_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8035_41 : X1 ≠ (M.op (M.op X1 X0) X1) := by
      first
      | (have i₁ := f8035_23
         have i₂ := f8035_25 X1
         grind)
      | exact superpose f8035_25 f8035_23
      | exact resolve f8035_23 f8035_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8035_42 : False := by
      first
      | (have r₁ := f8035_41
         have r₂ := f8035_37 X0 X1
         grind)
      | exact resolve f8035_41 f8035_37
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f8035_42
  have eq8074 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f8074_13 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f8074_14 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f8074_23 : X1 ≠ (M.op (M.op X1 X0) X1) := by grind
    have f8074_24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f8074_25 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f8074_14 X0
         grind)
      | (have r₁ := f8074_14 X0
         have r₂ := f8074_24
         grind)
      | exact resolve f8074_14 f8074_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8074_26 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X1) X0) X1) = X1 := by
      intro X0 X1
      first
      | (have j0 := f8074_13 X0 X1
         grind)
      | (have r₁ := f8074_13 X0 X1
         have r₂ := f8074_24
         grind)
      | exact resolve f8074_13 f8074_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8074_27 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f8074_26 X0 X1
         have i₂ := f8074_25 X1
         grind)
      | exact superpose f8074_25 f8074_26
      | exact resolve f8074_26 f8074_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8074_30 : X1 ≠ X1 := by
      first
      | (have i₁ := f8074_23
         have i₂ := f8074_27 X0 X1
         grind)
      | exact superpose f8074_27 f8074_23
      | (have r₁ := f8074_23
         have r₂ := f8074_27 X0 X1
         grind)
      | exact resolve f8074_23 f8074_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8074_31 : False := by grind
    exact f8074_31
  clear eq7974 eq8035
  have eq8441 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) = (M.op X0 (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq558 eq8074
    | exact resolve eq8074 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq8074
  have eq8585 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7477 eq8441
    | exact resolve eq8441 eq7477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7477 eq8441
  have eq8596 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f8596_13 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f8596_14 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f8596_23 : (σ y) ≠ (M.op X0 (σ y)) := by grind
    have f8596_24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f8596_25 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
      intro X0
      first
      | (have j0 := f8596_14 X0
         grind)
      | (have r₁ := f8596_14 X0
         have r₂ := f8596_24
         grind)
      | exact resolve f8596_14 f8596_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8596_26 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
      intro X0
      first
      | (have j0 := f8596_13 X0
         grind)
      | (have r₁ := f8596_13 X0
         have r₂ := f8596_24
         grind)
      | exact resolve f8596_13 f8596_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8596_27 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
      intro X0
      first
      | (have i₁ := f8596_26 X0
         have i₂ := f8596_25 X0
         grind)
      | exact superpose f8596_25 f8596_26
      | exact resolve f8596_26 f8596_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8596_28 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f8596_23
         have i₂ := f8596_27 X0
         grind)
      | exact superpose f8596_27 f8596_23
      | (have r₁ := f8596_23
         have r₂ := f8596_27 X0
         grind)
      | exact resolve f8596_23 f8596_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8596_29 : False := by grind
    exact f8596_29
  clear eq7623 eq8585
  have eq8705 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8596 eq26
    | (have j1 := eq8596 (σ x)
       grind)
    | exact resolve eq26 eq8596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8596
  have eq8729 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8705
  have eq8912 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq8729 eq27
    | exact resolve eq27 eq8729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8729
  have eq8941 : False := by grind
  exact eq8941

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pxy_x_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
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
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X2)) ≠ X0 ∨ (k (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) (M.op X2 X2)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq80
    | (have j0 := eq80 X0 (σ X1)
       grind)
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq44
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq44 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq195 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq80 (σ X0) sF1
       grind)
    | exact superpose eq80 eq41
    | (have j1 := eq80 X0 (σ (M.op x y))
       grind)
    | exact resolve eq41 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq216 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq80 (τ X0) X1
       grind)
    | exact superpose eq80 eq34
    | (have j1 := eq80 X0 X1
       grind)
    | exact resolve eq34 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq319 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq406 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq52 X0 X0 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op X2 X2)) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) (σ X0) X2
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq14
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq14 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq693 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op x x) x (M.op x x)
       have i₂ := eq52 x x x x
       grind)
    | exact superpose eq52 eq65
    | (have r₁ := eq65 (M.op x x) (M.op x x) (M.op (M.op x x) (M.op x x))
       have r₂ := eq52 (M.op x x) (M.op x x) (M.op x x) x
       grind)
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq110 eq80
    | (have j0 := eq80 x (σ y)
       grind)
    | exact resolve eq80 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq765
    | exact resolve eq765 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq769 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq766
       have r₂ := eq27
       grind)
    | exact resolve eq766 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq775 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq769 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq769
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq769
       grind)
    | exact resolve eq13 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq789 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq775
  have eq919 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq789 eq85
    | exact resolve eq85 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq789
  have eq923 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq919
    | exact resolve eq919 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq1004 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq80 y y
       have i₂ := eq923
       grind)
    | exact superpose eq923 eq80
    | (have j0 := eq80 x y
       grind)
    | exact resolve eq80 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq1005 : y = (M.op y y) := by grind
  clear eq1004
  have eq1009 : ∀ X0 : G, y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1005
       have i₂ := eq333 X0 y
       grind)
    | (have i₁ := eq1005
       have i₂ := eq333 y X0
       grind)
    | exact superpose eq333 eq1005
    | exact resolve eq1005 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq1016 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 y
       have i₂ := eq1005
       grind)
    | exact superpose eq1005 eq14
    | exact resolve eq14 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1017 : y = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq1005
       grind)
    | exact superpose eq1005 eq50
    | exact resolve eq50 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1025 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq346 y X0
       have i₂ := eq1005
       grind)
    | exact superpose eq1005 eq346
    | exact resolve eq346 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1048 : ∀ X0 X2 X3 : G, (M.op (M.op X0 y) (M.op (M.op X2 X0) (M.op X3 X3))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq52 X0 X2 X3 x
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq52
    | exact resolve eq52 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1061 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X0 X0 X1
       have i₂ := eq1009 (M.op X0 X0)
       grind)
    | exact superpose eq1009 eq52
    | exact resolve eq52 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1070 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1061 X0 x
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq1061
    | exact resolve eq1061 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1077 : ∀ X0 X2 : G, (M.op (M.op X0 y) (M.op (M.op X2 X0) y)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1048 X0 X2 x
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq1048
    | exact resolve eq1048 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1087 : ∀ X0 X1 : G, y ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq1009 X1
       grind)
    | exact superpose eq1009 eq693
    | (have j0 := eq693 X0 X1
       grind)
    | (have r₁ := eq693 y X0
       have r₂ := eq1009 X0
       grind)
    | exact resolve eq693 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq1088 : ∀ X0 : G, y ≠ X0 ∨ y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1087 X0 x
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq1087
    | (have j0 := eq1087 X0 x
       grind)
    | (have r₁ := eq1087 (M.op X0 X0) x
       have r₂ := eq1009 X0
       grind)
    | exact resolve eq1087 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1089 : y = (k y y) := by
    first
    | (have j0 := eq1088 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1091 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1089
       grind)
    | exact superpose eq1089 eq73
    | exact resolve eq73 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1089
  have eq1095 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1091
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1091
    | exact resolve eq1091 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1098 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1095 eq80
    | (have j0 := eq80 x (σ y)
       grind)
    | exact resolve eq80 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1095
  have eq1099 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1098
  have eq1101 : y = (σ y) := by
    first
    | (have i₁ := eq1099
       have i₂ := eq1009 sF3
       grind)
    | exact superpose eq1009 eq1099
    | exact resolve eq1099 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1104 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1101 eq26
    | exact resolve eq26 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1105 : y = (τ y) := by
    first
    | exact superpose eq1101 eq29
    | exact resolve eq29 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1222 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 X0)) (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq1017 eq14
    | exact resolve eq14 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1223 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq1222 X0
       have i₂ := eq1025 (M.op X0 X0)
       grind)
    | exact superpose eq1025 eq1222
    | exact resolve eq1222 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025 eq1222
  have eq1226 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1223 x
       have i₂ := eq346 x (M.op sF0 y)
       grind)
    | exact superpose eq346 eq1223
    | exact resolve eq1223 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1548 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ y = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq1009 sF1
       grind)
    | exact superpose eq1009 eq195
    | (have j0 := eq195 X0
       grind)
    | exact resolve eq195 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1624 : (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq1548 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1548
    | (have j0 := eq1548 x
       grind)
    | exact resolve eq1548 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1636 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq45 eq1624
    | exact resolve eq1624 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624
  have eq3442 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 x) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1077 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1077
    | (have j0 := eq1077 x X0
       grind)
    | exact resolve eq1077 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3446 : ∀ X0 : G, (M.op x (M.op (M.op X0 (M.op x y)) y)) = X0 := by
    intro X0
    first
    | exact superpose eq1226 eq1077
    | exact resolve eq1077 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3448 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) y)) = X0 := by
    intro X0
    first
    | exact superpose eq1104 eq1077
    | exact resolve eq1077 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3561 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op X0 x) y) y) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq3442 eq1077
    | exact resolve eq1077 eq3442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3442
  have eq3570 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq3561 X0
       have i₂ := eq1070 (M.op X0 x)
       grind)
    | exact superpose eq1070 eq3561
    | exact resolve eq3561 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3561
  have eq3595 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op X0 (M.op x y)) y) y) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq3446 eq1077
    | exact resolve eq1077 eq3446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq3604 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq3595 X0
       have i₂ := eq1070 (M.op X0 sF0)
       grind)
    | exact superpose eq1070 eq3595
    | exact resolve eq3595 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3595
  have eq3615 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq1009 X1
       grind)
    | exact superpose eq1009 eq216
    | (have j0 := eq216 X0 X1
       grind)
    | exact resolve eq216 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq3629 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op X0 (σ x)) y) y) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq3448 eq1077
    | exact resolve eq1077 eq3448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077 eq3448
  have eq3638 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq3629 X0
       have i₂ := eq1070 (M.op X0 sF2)
       grind)
    | exact superpose eq1070 eq3629
    | exact resolve eq3629 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3629
  have eq3693 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op (M.op x X0) y) y)) := by
    intro X0
    first
    | (have i₁ := eq3570 (M.op (M.op x X0) y)
       have i₂ := eq1016 x X0
       grind)
    | exact superpose eq1016 eq3570
    | exact resolve eq3570 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3723 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x y) y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1016 (M.op X0 x) (M.op X0 y)
       have i₂ := eq3570 X0
       grind)
    | exact superpose eq3570 eq1016
    | exact resolve eq1016 eq3570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3570
  have eq3731 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq1226 eq3723
    | exact resolve eq3723 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723
  have eq3748 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq3693 X0
       have i₂ := eq1070 (M.op x X0)
       grind)
    | exact superpose eq1070 eq3693
    | exact resolve eq3693 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693
  have eq3791 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq28 eq3615
    | (have j0 := eq3615 X0 X0
       grind)
    | exact resolve eq3615 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3802 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (k X0 (σ X1))) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (τ X0) X1)
       have i₂ := eq3615 X0 X1
       grind)
    | exact superpose eq3615 eq16
    | (have j1 := eq3615 X0 X1
       grind)
    | exact resolve eq16 eq3615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3615
  have eq3822 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3802 X0 X1
       have i₂ := eq219 X0 X1
       grind)
    | exact superpose eq219 eq3802
    | (have j0 := eq3802 X0 X1
       grind)
    | exact resolve eq3802 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq3802
  have eq3830 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq35 eq3791
    | (have j0 := eq3791 X0
       grind)
    | exact resolve eq3791 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3791
  have eq4798 : x = (M.op (M.op x (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq3604 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3604
    | (have j0 := eq3604 x
       grind)
    | exact resolve eq3604 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4864 : ∀ X0 : G, (M.op x y) ≠ (M.op x (M.op X0 X0)) ∨ (M.op x y) = (k (M.op x (M.op X0 X0)) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq4798 eq65
    | exact resolve eq65 eq4798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq4798
  have eq4870 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x (M.op X0 X0)) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4864 X0
       have i₂ := eq1009 X0
       grind)
    | exact superpose eq1009 eq4864
    | (have j0 := eq4864 X0
       grind)
    | exact resolve eq4864 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4864
  have eq4875 : ∀ X0 : G, (M.op x y) = (k (M.op x (M.op X0 X0)) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq4870 X0
       grind)
    | (have r₁ := eq4870 X0
       have r₂ := eq18
       grind)
    | exact resolve eq4870 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4870
  have eq4877 : (M.op x y) = (k (M.op x y) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq4875 x
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq4875
    | exact resolve eq4875 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4875
  have eq4878 : (M.op x y) = (k (M.op x y) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq4877
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4877
    | exact resolve eq4877 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4877
  have eq5005 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (M.op (σ x) X0) y) y)) := by
    intro X0
    first
    | (have i₁ := eq3638 (M.op (M.op sF2 x) y)
       have i₂ := eq1016 sF2 x
       grind)
    | exact superpose eq1016 eq3638
    | exact resolve eq3638 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq5023 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) (σ x)) x) := by
    first
    | exact superpose eq1226 eq3638
    | exact resolve eq3638 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq3638
  have eq5062 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq5005 X0
       have i₂ := eq1070 (M.op sF2 X0)
       grind)
    | exact superpose eq1070 eq5005
    | exact resolve eq5005 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5005
  have eq5215 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) y)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq406 X0 X1 X2 x
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq406
    | exact resolve eq406 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq5216 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X0 y)) y)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq5215 X0 x X2
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq5215
    | exact resolve eq5215 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5215
  have eq5372 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op (M.op X0 (M.op X1 y)) y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op (M.op x (M.op X0 y)) y)
       have i₂ := eq5216 X0 x
       grind)
    | exact superpose eq5216 eq13
    | (have r₁ := eq13 x (M.op (M.op x (M.op x y)) y)
       have r₂ := eq5216 x x
       grind)
    | exact resolve eq13 eq5216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5373 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) y) = (M.op (M.op X0 (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 (M.op X1 y)) y) X1 X2
       have i₂ := eq5216 X1 X0
       grind)
    | exact superpose eq5216 eq14
    | exact resolve eq14 eq5216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5388 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) y) = (M.op (M.op X0 y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5373 X0 X1 x
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq5373
    | exact resolve eq5373 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5373
  have eq5633 : (M.op (M.op (M.op x y) (σ x)) y) = (M.op x (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5023 eq3731
    | exact resolve eq3731 eq5023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3731 eq5023
  have eq6260 : x = (M.op (M.op (M.op (M.op x y) (σ x)) (M.op x y)) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5633 eq3604
    | exact resolve eq3604 eq5633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3604 eq5633
  have eq7026 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq413 X0 X1 X2 X3 x
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq413
    | exact resolve eq413 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq7027 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 y) (M.op X0 y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7026 X0 X1 x X3
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq7026
    | exact resolve eq7026 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7026
  have eq7028 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op (M.op X1 y) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq7027 X0 X1 x
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq7027
    | exact resolve eq7027 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7027
  have eq7087 : ∀ X0 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7028 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7028
    | (have j0 := eq7028 x X0
       grind)
    | exact resolve eq7028 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7090 : ∀ X0 : G, (M.op (M.op X0 (σ x)) y) = (M.op (M.op X0 y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1104 eq7028
    | exact resolve eq7028 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7113 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op (M.op X0 y) y))) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5216 (M.op X0 y) X1
       have i₂ := eq7028 (M.op X1 (M.op (M.op X0 y) y)) X0
       grind)
    | exact superpose eq7028 eq5216
    | exact resolve eq5216 eq7028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216 eq7028
  have eq7156 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7113 X0 X1
       have i₂ := eq1070 X0
       grind)
    | exact superpose eq1070 eq7113
    | exact resolve eq7113 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7113
  have eq8174 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) y) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 X1 x
       have i₂ := eq1009 x
       grind)
    | exact superpose eq1009 eq519
    | (have j0 := eq519 X0 X1 x
       grind)
    | exact resolve eq519 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq8175 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) y) (σ X0)) ∨ (σ X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq8174 X0 X1
       have i₂ := eq1009 (σ X1)
       grind)
    | exact superpose eq1009 eq8174
    | (have j0 := eq8174 X0 X1
       grind)
    | exact resolve eq8174 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009 eq8174
  have eq8234 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (M.op (k (σ X0) X1) y) (σ X0)) ∨ y = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8175 X0 (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq8175
    | (have j0 := eq8175 X0 (τ X1)
       grind)
    | exact resolve eq8175 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq8175
  have eq8354 : ∀ X0 X1 : G, (M.op (M.op (k (σ X0) X1) y) (σ X0)) = X1 ∨ y = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8234 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq8234
    | (have j0 := eq8234 X0 X1
       grind)
    | exact resolve eq8234 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8234
  have eq8433 : ∀ X0 X1 : G, (M.op (M.op (k (σ X0) X1) y) (σ X0)) = X1 ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8354 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq8354
    | (have j0 := eq8354 X0 X1
       grind)
    | exact resolve eq8354 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8354
  have eq13152 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3822 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3822
    | (have j0 := eq3822 X0 X1
       grind)
    | exact resolve eq3822 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3822
  have eq13423 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq45 eq3830
    | (have j0 := eq3830 (M.op x y)
       grind)
    | exact resolve eq3830 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3830
  have eq13820 : (k (σ (M.op x y)) (k (σ x) (σ (M.op x y)))) = (σ (k (M.op x y) (M.op x (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13423 eq37
    | exact resolve eq37 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq13423
  have eq13857 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4878 eq13820
    | exact resolve eq13820 eq4878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4878 eq13820
  have eq13862 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq13857
    | exact resolve eq13857 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13857
  have eq13865 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq1636 eq13862
    | exact resolve eq13862 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636 eq13862
  have eq16871 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op (M.op X0 y) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5372 X0 X1
       have i₂ := eq5388 X0 X1
       grind)
    | exact superpose eq5388 eq5372
    | (have j0 := eq5372 X0 X1
       grind)
    | (have r₁ := eq5372 (M.op (M.op X0 (M.op X1 y)) y) (M.op (M.op X0 y) X1)
       have r₂ := eq5388 X0 X1
       grind)
    | (have r₁ := eq5372 (M.op (M.op X0 y) X1) (M.op (M.op X0 (M.op X1 y)) y)
       have r₂ := eq5388 X0 X1
       grind)
    | exact resolve eq5372 eq5388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5372 eq5388
  have eq16872 : ∀ X0 : G, (k X0 (M.op (M.op X0 y) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq16871 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16871
  have eq16966 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op (σ X0) y) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq319 X0 (M.op (M.op (σ X0) y) (σ X0))
       have i₂ := eq16872 (σ X0)
       grind)
    | exact superpose eq16872 eq319
    | exact resolve eq319 eq16872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq16872
  have eq16967 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ X0) y) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16966 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq16966
    | exact resolve eq16966 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16966
  have eq17192 : ∀ X0 X1 : G, (M.op (M.op (k X0 X1) y) X0) = X1 ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8433 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8433
    | (have j0 := eq8433 X0 X1
       grind)
    | exact resolve eq8433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8433
  have eq24684 : ∀ X0 : G, (M.op (M.op (k (M.op x y) X0) x) y) = X0 ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq7087 eq17192
    | (have j0 := eq17192 X0 X0
       grind)
    | exact resolve eq17192 eq7087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7087 eq17192
  have eq88082 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq13865 eq13152
    | (have j0 := eq13152 x (M.op (σ x) (σ (M.op x y)))
       grind)
    | exact resolve eq13152 eq13865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13152 eq13865
  have eq88088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq5062 eq88082
    | exact resolve eq88082 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5062 eq88082
  have eq88099 : y = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ (M.op x y)) := by
    first
    | (have r₁ := eq88088
       have r₂ := eq27
       grind)
    | exact resolve eq88088 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88088
  have eq88558 : (σ x) = (M.op (M.op (σ (M.op x y)) y) y) ∨ y = (M.op x y) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq88099 eq7156
    | exact resolve eq7156 eq88099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88099
  have eq88581 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq88558
       have i₂ := eq1070 sF1
       grind)
    | exact superpose eq1070 eq88558
    | exact resolve eq88558 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88558
  have eq88608 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq88581 eq28
    | exact resolve eq28 eq88581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq88581
  have eq88939 : y = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq88608
    | exact resolve eq88608 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88608
  have eq89450 : (M.op x y) = (τ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88939 eq30
    | exact resolve eq30 eq88939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq88939
  have eq89554 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89450
       have i₂ := eq1105
       grind)
    | exact superpose eq1105 eq89450
    | exact resolve eq89450 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq89450
  have eq89555 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq89554
  have eq90145 : x = (M.op (M.op (M.op y (σ x)) y) (M.op x (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq89555 eq6260
    | exact resolve eq6260 eq89555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6260 eq89555
  have eq90362 : x = (M.op (M.op (M.op y y) (M.op (σ x) (σ y))) (M.op x (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7090 eq90145
    | exact resolve eq90145 eq7090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7090 eq90145
  have eq90488 : x = (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90362
       have i₂ := eq346 y sF4
       grind)
    | exact superpose eq346 eq90362
    | exact resolve eq90362 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90362
  have eq90570 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90488
       have i₂ := eq3748 sF4
       grind)
    | exact superpose eq3748 eq90488
    | exact resolve eq90488 eq3748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748 eq90488
  have eq90571 : x = (M.op x y) := by grind
  clear eq90570
  have eq90634 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq90571 eq20
    | exact resolve eq20 eq90571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq90796 : ∀ X0 : G, (M.op (M.op (k x X0) x) y) = X0 ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq90571 eq24684
    | (have j0 := eq24684 X0
       grind)
    | exact resolve eq24684 eq90571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24684 eq90571
  have eq90968 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq90634
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq90634
    | exact resolve eq90634 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90634
  have eq91121 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq90968 eq1104
    | exact resolve eq1104 eq90968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq157709 : (M.op (M.op x x) y) = (τ (M.op (M.op (σ x) y) (σ x))) ∨ y = (τ (M.op (M.op (σ x) y) (σ x))) := by
    first
    | (have i₁ := eq90796 (τ (M.op (M.op (σ x) y) (σ x)))
       have i₂ := eq16967 x
       grind)
    | exact superpose eq16967 eq90796
    | (have j0 := eq90796 (τ (M.op (M.op (σ x) y) (σ x)))
       grind)
    | exact resolve eq90796 eq16967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16967 eq90796
  have eq157843 : (M.op (M.op x x) y) = (τ (M.op (M.op (σ x) y) (σ x))) ∨ y = (τ (M.op (M.op (σ x) y) (σ x))) := by
    first
    | (have i₁ := eq157709
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq157709
    | exact resolve eq157709 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157709
  have eq157871 : (M.op (M.op x x) y) = (τ (M.op (M.op (σ (M.op x y)) y) (σ (M.op x y)))) ∨ y = (τ (M.op (M.op (σ x) y) (σ x))) := by
    first
    | exact superpose eq90968 eq157843
    | exact resolve eq157843 eq90968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157843
  have eq157878 : (M.op (M.op x x) y) = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (τ (M.op (M.op (σ x) y) (σ x))) := by
    first
    | exact superpose eq91121 eq157871
    | exact resolve eq157871 eq91121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157871
  have eq157880 : y = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (τ (M.op (M.op (σ x) y) (σ x))) := by
    first
    | (have i₁ := eq157878
       have i₂ := eq346 x y
       grind)
    | exact superpose eq346 eq157878
    | exact resolve eq157878 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq157878
  have eq157881 : y = (τ (M.op (M.op (σ x) y) (σ x))) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq157880
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq157880
    | exact resolve eq157880 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq157880
  have eq157882 : y = (τ (M.op (M.op (σ (M.op x y)) y) (σ (M.op x y)))) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq90968 eq157881
    | exact resolve eq157881 eq90968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90968 eq157881
  have eq157883 : y = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq91121 eq157882
    | exact resolve eq157882 eq91121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91121 eq157882
  have eq157884 : y = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) := by grind
  clear eq157883
  have eq157886 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq157884 eq15
    | exact resolve eq15 eq157884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157884
  have eq158184 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq157886
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq157886
    | exact resolve eq157886 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq157886
  have eq158266 : y = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1101 eq158184
    | exact resolve eq158184 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101 eq158184
  have eq158402 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) y) y) := by
    first
    | exact superpose eq158266 eq7156
    | exact resolve eq7156 eq158266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7156 eq158266
  have eq158421 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq158402
       have i₂ := eq1070 sF1
       grind)
    | exact superpose eq1070 eq158402
    | exact resolve eq158402 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq158402
  have eq158450 : False := by grind
  exact eq158450

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_y_pyy_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
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
  have eq35 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
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
  have eq39 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39
    | exact resolve eq39 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq89 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq117 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq35 x x X1
       have i₂ := eq35 x x X0
       grind)
    | exact superpose eq35 eq35
    | exact resolve eq35 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    grind
  have eq123 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45 X2
       have i₂ := eq35 X0 X1 (σ X2)
       grind)
    | exact superpose eq35 eq45
    | exact resolve eq45 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq126 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq35 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq35 eq9
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X2 : G, (k (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq123 X0 x X2
       have i₂ := eq126 x X0
       grind)
    | exact superpose eq126 eq123
    | exact resolve eq123 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq132 : ∀ X0 X2 : G, (k (M.op X0 X0) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq120 X0 x X2
       have i₂ := eq126 x X0
       grind)
    | exact superpose eq126 eq120
    | exact resolve eq120 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq150 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq34 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq34 X1 X0 X2 X4
       grind)
    | exact superpose eq34 eq34
    | exact resolve eq34 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X1 X1 (M.op X1 X1) X2
       have i₂ := eq35 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq35 eq34
    | exact resolve eq34 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq35
  have eq166 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq150 X0 X1 x x X4 X5
       have i₂ := eq153 x (M.op X0 X1) x
       grind)
    | exact superpose eq153 eq150
    | exact resolve eq150 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq259 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X0
       have i₂ := eq117 X0 (σ X0)
       grind)
    | (have i₁ := eq91 X0 X0
       have i₂ := eq117 (σ X0) X1
       grind)
    | exact superpose eq117 eq91
    | exact resolve eq91 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq16
    | (have j1 := eq91 x x
       grind)
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq91 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq277 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq291 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq404 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ (M.op X1 X1)) X0
       have i₂ := eq129 X1 (σ X0)
       grind)
    | exact superpose eq129 eq23
    | exact resolve eq23 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq129
  have eq407 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq404 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq404
    | exact resolve eq404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq1285 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X4 X4)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 X3)) (M.op X2 X0) X4
       have i₂ := eq166 X2 X0 X1 X3
       grind)
    | exact superpose eq166 eq9
    | exact resolve eq9 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq1288 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1285 X0 x X2 X3 x
       have i₂ := eq153 x X0 x
       grind)
    | exact superpose eq153 eq1285
    | exact resolve eq1285 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1285
  have eq1387 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1288 X3 X1 x
       have i₂ := eq1288 X0 X1 x
       grind)
    | (have i₁ := eq1288 X0 X0 X0
       have i₂ := eq1288 X0 X0 X3
       grind)
    | exact superpose eq1288 eq1288
    | exact resolve eq1288 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1695 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq277 (M.op X0 X0)
       have i₂ := eq132 X0 (M.op X0 X0)
       grind)
    | exact superpose eq132 eq277
    | (have j0 := eq277 (M.op X0 X0)
       grind)
    | exact resolve eq277 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq1720 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq3220 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X1 (M.op X0 X0)
       have i₂ := eq132 X0 (M.op X0 X0)
       grind)
    | exact superpose eq132 eq291
    | (have j0 := eq291 X1 (M.op X0 X0)
       grind)
    | exact resolve eq291 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq3230 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq407 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq407 eq291
    | (have j0 := eq291 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq291 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq3318 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X1)
       have i₂ := eq291 X0 (τ X1)
       grind)
    | exact superpose eq291 eq19
    | (have j1 := eq291 X0 (τ X1)
       grind)
    | exact resolve eq19 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3338 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3344 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq3230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230
  have eq3352 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3220 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3220
  have eq3362 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3318 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3318
    | (have j0 := eq3318 X0 X1
       grind)
    | exact resolve eq3318 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318
  have eq3399 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3344 X0 X1
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq3344
    | exact resolve eq3344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq3408 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3362 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3362
    | (have j0 := eq3362 X0 X1
       grind)
    | exact resolve eq3362 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362
  have eq3499 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1387 X1 X2 X2
       have i₂ := eq3352 X0 X2
       grind)
    | exact superpose eq3352 eq1387
    | exact resolve eq1387 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq3517 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq3352 X0 (M.op X1 X1)
       grind)
    | exact superpose eq3352 eq9
    | exact resolve eq9 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3924 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (τ (σ (k X0 X0))) ∨ (M.op X2 X2) = (σ X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3399 X2 X1
       have i₂ := eq291 X2 X0
       grind)
    | exact superpose eq291 eq3399
    | (have j1 := eq291 X2 X0
       grind)
    | exact resolve eq3399 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq4007 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq3399 X0 (M.op X1 X1)
       grind)
    | exact superpose eq3399 eq9
    | exact resolve eq9 eq3399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4021 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3517 X1 (σ (M.op X1 X1))
       have i₂ := eq3399 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq3399 eq3517
    | exact resolve eq3517 eq3399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399
  have eq4084 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = (σ X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3924 X0 X1 X2
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq3924
    | (have j0 := eq3924 X0 X1 X2
       grind)
    | exact resolve eq3924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3924
  have eq4546 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | (have j0 := eq89 X1 X1
       grind)
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq4641 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4546 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4546
    | (have j0 := eq4546 X1 X1
       grind)
    | exact resolve eq4546 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4546
  have eq13068 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (σ (k X0 X0)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3352 X2 X1
       have i₂ := eq3408 X2 X0
       grind)
    | exact superpose eq3408 eq3352
    | (have j1 := eq3408 X1 (σ (k X0 X0))
       grind)
    | exact resolve eq3352 eq3408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq13216 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3408 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3408
  have eq13747 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op X1 X1))) = (M.op X0 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3517 X2 (M.op X0 (σ (M.op X2 X2)))
       have i₂ := eq3499 X1 (σ (M.op X2 X2)) X0
       grind)
    | exact superpose eq3499 eq3517
    | exact resolve eq3517 eq3499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3517
  have eq54755 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (σ X1) ∨ (M.op X2 X2) = (σ X1) ∨ (M.op X3 X3) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3338 X2 X1
       have i₂ := eq13068 X1 X0 X3
       grind)
    | exact superpose eq13068 eq3338
    | (have j0 := eq3338 X2 X1
       have j1 := eq13068 (σ X1) X1 X2
       grind)
    | exact resolve eq3338 eq13068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338 eq13068
  have eq73494 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 ∨ (σ X1) = (M.op X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13216 X2 X1
       have i₂ := eq4084 X1 X0 X3
       grind)
    | exact superpose eq4084 eq13216
    | (have j0 := eq13216 X2 X1
       have j1 := eq4084 X1 X1 X3
       grind)
    | (have r₁ := eq13216 X0 (M.op X1 X1)
       have r₂ := eq4084 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq13216 eq4084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4084 eq13216
  have eq77831 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq261
       have i₂ := eq4641 y x
       grind)
    | exact superpose eq4641 eq261
    | (have j1 := eq4641 (σ x) (σ x)
       grind)
    | (have r₁ := eq261
       have r₂ := eq4641 y x
       grind)
    | exact resolve eq261 eq4641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq4641
  have eq77858 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq77831
  have eq77897 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq73494 x x x (σ x)
       grind)
    | (have r₁ := eq77858
       have r₂ := eq73494 (σ x) (σ x) x x
       grind)
    | (have r₁ := eq77858
       have r₂ := eq73494 (σ y) (σ x) x x
       grind)
    | (have r₁ := eq77858
       have r₂ := eq73494 x x x x
       grind)
    | exact resolve eq77858 eq73494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73494 eq77858
  have eq77915 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq54755 x x (σ x) x
       grind)
    | (have r₁ := eq77897
       have r₂ := eq54755 (σ x) x x x
       grind)
    | (have r₁ := eq77897
       have r₂ := eq54755 (σ y) x x x
       grind)
    | exact resolve eq77897 eq54755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54755 eq77897
  have eq78003 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1720 x
       have i₂ := eq77915
       grind)
    | exact superpose eq77915 eq1720
    | exact resolve eq1720 eq77915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720 eq77915
  have eq78134 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq78003
  have eq78162 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq117 (σ x) X0
       have i₂ := eq78134
       grind)
    | exact superpose eq78134 eq117
    | exact resolve eq117 eq78134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq78163 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq126 (σ x) X0
       have i₂ := eq78134
       grind)
    | exact superpose eq78134 eq126
    | exact resolve eq126 eq78134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq78280 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4007 (σ x) X0
       have i₂ := eq78134
       grind)
    | exact superpose eq78134 eq4007
    | exact resolve eq4007 eq78134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4007
  have eq78288 : ∀ X0 : G, (σ (M.op X0 X0)) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4021 (σ x) X0
       have i₂ := eq78134
       grind)
    | exact superpose eq78134 eq4021
    | exact resolve eq4021 eq78134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021
  have eq78350 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = (M.op X0 (σ (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq13747 X0 (σ x) X1
       have i₂ := eq78134
       grind)
    | exact superpose eq78134 eq13747
    | exact resolve eq13747 eq78134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13747
  have eq78385 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3499 X0 (σ x) (σ x)
       have i₂ := eq78134
       grind)
    | exact superpose eq78134 eq3499
    | exact resolve eq3499 eq78134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3499
  have eq78400 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq78385 X0
       have i₂ := eq78134
       grind)
    | exact superpose eq78134 eq78385
    | exact resolve eq78385 eq78134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78134 eq78385
  have eq78436 : ∀ X0 : G, x = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq78288 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq78288
    | exact resolve eq78288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78288
  have eq78443 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78280 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq78280
    | exact resolve eq78280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78280
  have eq78512 : (σ x) = (M.op (σ x) (σ (σ x))) := by
    first
    | (have i₁ := eq78400 x
       have i₂ := eq78350 (σ x) x
       grind)
    | exact superpose eq78350 eq78400
    | exact resolve eq78400 eq78350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78350 eq78400
  have eq78534 : x = (σ (σ x)) := by
    first
    | (have i₁ := eq78436 x
       have i₂ := eq78162 x
       grind)
    | exact superpose eq78162 eq78436
    | exact resolve eq78436 eq78162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78162 eq78436
  have eq78565 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq78512
       have i₂ := eq78163 (σ (σ x))
       grind)
    | exact superpose eq78163 eq78512
    | exact resolve eq78512 eq78163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78163 eq78512
  have eq78591 : x = (σ x) := by
    first
    | (have i₁ := eq78565
       have i₂ := eq78534
       grind)
    | exact superpose eq78534 eq78565
    | exact resolve eq78565 eq78534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78534 eq78565
  have eq79508 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78591
       grind)
    | exact superpose eq78591 eq16
    | exact resolve eq16 eq78591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78591
  have eq79546 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq79508
       have i₂ := eq78443 (σ y)
       grind)
    | exact superpose eq78443 eq79508
    | exact resolve eq79508 eq78443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79508
  have eq79556 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq79546
       have i₂ := eq78443 y
       grind)
    | exact superpose eq78443 eq79546
    | exact resolve eq79546 eq78443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78443 eq79546
  have eq79557 : False := by grind
  exact eq79557

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_y_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X1 X1)) (M.op (M.op x y) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq192 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq343 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq393 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq38
    | exact resolve eq38 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq393 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq393
    | exact resolve eq393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq445 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq343 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq343
    | exact resolve eq343 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq343
  have eq467 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq445 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq445
    | exact resolve eq445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x x X1
       have i₂ := eq178 x x X0
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X3 ∨ (k X3 X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X2
       have i₂ := eq178 X0 X1 X2
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op (M.op X1 X1) X0)) X2
       have r₂ := eq178 X0 X1 X2
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 X2
       have i₂ := eq178 X0 X1 (σ X2)
       grind)
    | exact superpose eq178 eq467
    | exact resolve eq467 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq707 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq425 X2
       have i₂ := eq178 X0 X1 (τ X2)
       grind)
    | exact superpose eq178 eq425
    | exact resolve eq425 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq709 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 (M.op X1 X1)
       have i₂ := eq178 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq711 : ∀ X0 X2 : G, (k (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq707 X0 x X2
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq707
    | exact resolve eq707 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq712 : ∀ X0 X2 : G, (k (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq706 X0 x X2
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq706
    | exact resolve eq706 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq719 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X3 ∨ (k X3 X2) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq699 X0 x X2 X3
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq699
    | (have j0 := eq699 X0 x X2 X3
       grind)
    | (have r₁ := eq699 (M.op X0 X0) x X2 (M.op (M.op x x) (M.op X0 X0))
       have r₂ := eq709 X0 (M.op (M.op x x) (M.op X0 X0))
       grind)
    | (have r₁ := eq699 X0 x X2 (M.op (M.op X0 X0) (M.op X0 (M.op (M.op x x) X0)))
       have r₂ := eq709 X0 (M.op X0 (M.op (M.op x x) X0))
       grind)
    | exact resolve eq699 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq709
  have eq829 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ (M.op X1 X1))
       have i₂ := eq711 X1 (τ X0)
       grind)
    | exact superpose eq711 eq38
    | exact resolve eq38 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq842 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq829
    | exact resolve eq829 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq881 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq698 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq698 X0 X1
       grind)
    | exact superpose eq698 eq11
    | (have j0 := eq11 (k X1 X1) X0
       grind)
    | exact resolve eq11 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq887 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq888 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq881 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq1719 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq887
       grind)
    | exact superpose eq887 eq40
    | exact resolve eq40 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq887
  have eq1720 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1719
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1719
    | exact resolve eq1719 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq1722 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1720
    | exact resolve eq1720 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720
  have eq2219 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 X1 (σ (M.op X1 X1))
       have i₂ := eq947 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq947 eq711
    | (have j1 := eq947 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq711 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq2220 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq842 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq947 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq947 eq842
    | (have j1 := eq947 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact resolve eq842 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq2223 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X1 (τ (M.op X1 X1))
       have i₂ := eq947 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq947 eq712
    | (have j1 := eq947 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq712 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2230 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq947 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq2235 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2223 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq2238 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2220 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq2239 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219
  have eq2348 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq2239 (M.op X1 X1) X0
       grind)
    | exact superpose eq2239 eq16
    | exact resolve eq16 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq2517 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq2235 (M.op X1 X1) X0
       grind)
    | exact superpose eq2235 eq16
    | exact resolve eq16 eq2235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235
  have eq2921 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2348 X1 (σ (M.op X1 X1))
       have i₂ := eq2238 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq2238 eq2348
    | exact resolve eq2348 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq4967 : ∀ X0 X1 : G, (k x (σ (M.op X1 X1))) = (τ (k (σ x) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ (M.op X1 X1))
       have i₂ := eq2921 X1 X0
       grind)
    | exact superpose eq2921 eq44
    | exact resolve eq44 eq2921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921
  have eq4985 : ∀ X0 X1 : G, (k x (σ (M.op X1 X1))) = (k x (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq44 eq4967
    | exact resolve eq4967 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq4967
  have eq22449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1722 eq888
    | exact resolve eq888 eq1722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq1722
  have eq22460 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22449
       have r₂ := eq27
       grind)
    | exact resolve eq22449 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22449
  have eq22488 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq22460 eq712
    | exact resolve eq712 eq22460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq22460
  have eq22758 : ∀ X0 : G, (k x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq22488
    | exact resolve eq22488 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22488
  have eq22821 : ∀ X0 : G, (k x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22758 X0
       have j1 := eq719 X0 X0 x
       grind)
    | (have r₁ := eq22758 (M.op X0 X0)
       have r₂ := eq719 X0 x (k x (M.op X0 X0))
       grind)
    | (have r₁ := eq22758 X0
       have r₂ := eq719 y x x
       grind)
    | exact resolve eq22758 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq22758
  have eq22916 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k x (M.op X1 X1)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq4985 X1 X0
       have i₂ := eq22821 (σ (M.op X0 X0))
       grind)
    | exact superpose eq22821 eq4985
    | exact resolve eq4985 eq22821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4985
  have eq22927 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2230 X0 x
       have i₂ := eq22821 x
       grind)
    | exact superpose eq22821 eq2230
    | (have j0 := eq2230 X0 x
       grind)
    | (have r₁ := eq2230 X0 x
       have r₂ := eq22821 x
       grind)
    | exact resolve eq2230 eq22821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq22939 : ∀ X0 : G, x = (M.op X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22927 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22927
  have eq22953 : ∀ X0 : G, (k x x) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22939 eq22916
    | exact resolve eq22916 eq22939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22916
  have eq22968 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22821 eq22953
    | exact resolve eq22953 eq22821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22821 eq22953
  have eq22980 : x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22939 eq22968
    | exact resolve eq22968 eq22939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22968
  have eq22987 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22980
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22980
    | exact resolve eq22980 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22980
  have eq23282 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq22939 (M.op X0 X0)
       grind)
    | exact superpose eq22939 eq16
    | exact resolve eq16 eq22939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22939
  have eq23344 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22987 eq23282
    | (have j0 := eq23282 y
       grind)
    | exact resolve eq23282 eq22987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22987 eq23282
  have eq24135 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23344 eq26
    | (have j1 := eq23344 (σ y)
       grind)
    | exact resolve eq26 eq23344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23344
  have eq24325 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq24135
  have eq24479 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq24325 eq192
    | exact resolve eq192 eq24325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq24325
  have eq31072 : ∀ X1 : G, (M.op (τ (σ x)) X1) = X1 ∨ y = (M.op x y) := by
    intro X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f31072_12 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
      intro X0 X1
      grind
    have f31072_13 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) ∨ y = (M.op x y) := by
      intro X0 X1
      grind
    have f31072_19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
      intro X0
      grind
    have f31072_21 : X1 ≠ (M.op (τ (σ x)) X1) := by grind
    have f31072_22 : y ≠ (M.op x y) := by grind
    have f31072_24 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) := by
      intro X0 X1
      first
      | (have j0 := f31072_13 X0 X1
         grind)
      | (have r₁ := f31072_13 X0 X1
         have r₂ := f31072_22
         grind)
      | exact resolve f31072_13 f31072_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f31072_25 : X1 ≠ (M.op x X1) := by
      first
      | (have i₁ := f31072_21
         have i₂ := f31072_19 x
         grind)
      | exact superpose f31072_19 f31072_21
      | exact resolve f31072_21 f31072_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f31072_62 : ∀ X1 : G, (M.op (τ (σ x)) X1) = X1 := by
      intro X1
      first
      | (have i₁ := f31072_12 (M.op (σ y) (M.op x x)) X1
         have i₂ := f31072_24 x x
         grind)
      | exact superpose f31072_24 f31072_12
      | exact resolve f31072_12 f31072_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f31072_65 : ∀ X1 : G, (M.op x X1) = X1 := by
      intro X1
      first
      | (have i₁ := f31072_62 X1
         have i₂ := f31072_19 x
         grind)
      | exact superpose f31072_19 f31072_62
      | exact resolve f31072_62 f31072_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f31072_68 : X1 ≠ X1 := by
      first
      | (have i₁ := f31072_25
         have i₂ := f31072_65 X1
         grind)
      | exact superpose f31072_65 f31072_25
      | (have r₁ := f31072_25
         have r₂ := f31072_65 X1
         grind)
      | exact resolve f31072_25 f31072_65
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f31072_76 : False := by grind
    exact f31072_76
  clear eq2517 eq24479
  have eq31296 : ∀ X1 : G, (M.op x X1) = X1 ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq29 eq31072
    | exact resolve eq31072 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31072
  have eq33651 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31296 y
       grind)
    | exact superpose eq31296 eq18
    | (have j1 := eq31296 y
       grind)
    | exact resolve eq18 eq31296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq31296
  have eq33873 : y = (M.op x y) := by grind
  clear eq33651
  have eq34042 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq33873
       grind)
    | exact superpose eq33873 eq24
    | exact resolve eq24 eq33873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq34046 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op (M.op x y) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X1 X0
       have i₂ := eq33873
       grind)
    | exact superpose eq33873 eq191
    | exact resolve eq191 eq33873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq33873
  have eq34062 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34042 eq20
    | exact resolve eq20 eq34042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq34042
  have eq53054 : ∀ X1 : G, (M.op (σ x) X1) = X1 := by
    intro X1
    first
    | exact superpose eq34046 eq2348
    | exact resolve eq2348 eq34046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348 eq34046
  have eq53323 : ∀ X1 : G, (M.op (σ x) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq53054 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53054
    | (have j0 := eq53054 X1
       grind)
    | exact resolve eq53054 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53054
  have eq56976 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53323 eq26
    | (have j1 := eq53323 (σ y)
       grind)
    | exact resolve eq26 eq53323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53323
  have eq57615 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq56976 eq27
    | exact resolve eq27 eq56976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq56976
  have eq57636 : False := by grind
  exact eq57636

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b a :=
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
    | (have i₁ := eq69 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq69
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
  have eq11149 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op (τ X0) (τ X0))) (σ (M.op X2 X2))) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
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
  have eq11211 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11149 X0 X1 X2
       have i₂ := eq586 (τ X0) (σ (M.op X2 X2))
       grind)
    | exact superpose eq586 eq11149
    | (have j0 := eq11149 X0 X1 X2
       grind)
    | exact resolve eq11149 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11149
  have eq11267 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11211 X0 X1 x
       have i₂ := eq586 x (σ X1)
       grind)
    | exact superpose eq586 eq11211
    | (have j0 := eq11211 X0 X1 x
       grind)
    | exact resolve eq11211 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq11211
  have eq11268 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11267
  have eq28281 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11268 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11268
    | exact resolve eq11268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11268
  have eq28667 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq28281 y x
       grind)
    | exact superpose eq28281 eq49
    | (have j1 := eq28281 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq28281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq28865 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq28667
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28667
    | exact resolve eq28667 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28667
  have eq28932 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq28865
    | exact resolve eq28865 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28865
  have eq28967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28932 eq28281
    | (have j0 := eq28281 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28281 eq28932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28281 eq28932
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
