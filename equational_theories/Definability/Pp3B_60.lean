import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_y_pyx_y_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq67
    | exact resolve eq67 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq67
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq391 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq391
    | (have j0 := eq391 (σ X0) (σ X1)
       grind)
    | exact resolve eq391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 X0
       have i₂ := eq391 X1 X0
       grind)
    | exact superpose eq391 eq392
    | (have j0 := eq392 X1 X0
       have j1 := eq391 (σ X1) (σ X0)
       grind)
    | exact resolve eq392 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3049 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq586 x y
       grind)
    | exact superpose eq586 eq16
    | (have j1 := eq586 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq586 x y
       grind)
    | exact resolve eq16 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq3075 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3049
  have eq3109 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3075
       grind)
    | exact superpose eq3075 eq16
    | exact resolve eq16 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3113 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3075
       grind)
    | exact superpose eq3075 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3075
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3075
       grind)
    | exact resolve eq13 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3118 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3113
  have eq3123 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3118
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq3118
    | exact resolve eq3118 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq3118
  have eq3126 : (σ x) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3123
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3123
    | exact resolve eq3123 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123
  have eq3127 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq391 eq3126
    | (have j1 := eq391 y x
       grind)
    | exact resolve eq3126 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3126
  have eq3128 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3127
       have r₂ := eq3109
       grind)
    | exact resolve eq3127 eq3109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127
  have eq3134 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90 x (σ y)
       have i₂ := eq3128
       grind)
    | exact superpose eq3128 eq90
    | (have j0 := eq90 x (σ y)
       grind)
    | (have r₁ := eq90 x (σ y)
       have r₂ := eq3128
       grind)
    | exact resolve eq90 eq3128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3128
  have eq3143 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3134
  have eq3151 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3143
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3143
    | exact resolve eq3143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3143
  have eq3157 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3075 eq3151
    | exact resolve eq3151 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075 eq3151
  have eq3161 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq391 eq3157
    | (have j1 := eq391 y x
       grind)
    | exact resolve eq3157 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq3157
  have eq3163 : x = (M.op x y) := by
    first
    | (have r₁ := eq3161
       have r₂ := eq3109
       grind)
    | exact resolve eq3161 eq3109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3109 eq3161
  have eq3165 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3163
       grind)
    | exact superpose eq3163 eq16
    | exact resolve eq16 eq3163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3167 : x ≠ x ∨ (M.op x x) = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3163
       grind)
    | exact superpose eq3163 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3163
       grind)
    | exact resolve eq13 eq3163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3172 : (M.op x x) = (M.op y x) ∨ x = (k y x) := by grind
  clear eq3167
  have eq3272 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3172
       grind)
    | exact superpose eq3172 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3172
       grind)
    | exact resolve eq12 eq3172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3172
  have eq3278 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq3272
  have eq3280 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq3278
       have i₂ := eq3163
       grind)
    | exact superpose eq3163 eq3278
    | exact resolve eq3278 eq3163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3163 eq3278
  have eq3281 : x = (k y x) := by grind
  clear eq3280
  have eq3286 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq392 y x
       have i₂ := eq3281
       grind)
    | exact superpose eq3281 eq392
    | (have j0 := eq392 y x
       grind)
    | exact resolve eq392 eq3281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq3281
  have eq3289 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3286
  have eq3294 : False := by grind
  exact eq3294

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation3880 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq370 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (τ X0) X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq409 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq420 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq409
    | (have j0 := eq409 X0 X1
       grind)
    | exact resolve eq409 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq426 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq403
    | (have j0 := eq403 X0 X1
       grind)
    | exact resolve eq403 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq1860 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq426 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq426
    | (have j0 := eq426 (σ X1) (σ X0)
       grind)
    | exact resolve eq426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq1952 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1860 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1860
    | (have j0 := eq1860 X0 X1
       grind)
    | exact resolve eq1860 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860
  have eq3809 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq420 X1 X0
       grind)
    | exact superpose eq420 eq10
    | (have j1 := eq420 X1 X0
       grind)
    | exact resolve eq10 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq3873 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3809 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq3809
    | (have j0 := eq3809 X0 X1
       grind)
    | exact resolve eq3809 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3809
  have eq17183 : ∀ X0 X1 : G, (σ (σ (k X1 X0))) ≠ (σ (σ (M.op X1 X1))) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1952 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq282254 : ∀ X0 X1 : G, (σ (σ (M.op (τ X0) (τ X0)))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17183 (τ X0) (τ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq17183
    | (have j0 := eq17183 (τ X0) (τ X1)
       grind)
    | exact resolve eq17183 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17183
  have eq282797 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (M.op (τ X0) (τ X0)))) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq282254 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq282254
    | (have j0 := eq282254 X0 X1
       grind)
    | exact resolve eq282254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282254
  have eq283089 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ (M.op X0 X0)))) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq282797 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq282797
    | (have j0 := eq282797 X0 X1
       grind)
    | exact resolve eq282797 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282797
  have eq283338 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq283089 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq283089
    | (have j0 := eq283089 X0 X1
       grind)
    | exact resolve eq283089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283089
  have eq283583 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq283338 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq283338
    | (have j0 := eq283338 X0 X1
       grind)
    | exact resolve eq283338 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283338
  have eq283785 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (σ (τ (k X0 X1)))) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq283583 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq283583
    | (have j0 := eq283583 X0 X1
       grind)
    | exact resolve eq283583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283583
  have eq283969 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq283785 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq283785
    | (have j0 := eq283785 X0 X1
       grind)
    | exact resolve eq283785 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283785
  have eq284110 : ∀ X0 X1 : G, (σ X1) = (σ (σ (τ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq283969 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq283969
    | (have j0 := eq283969 X0 X1
       grind)
    | exact resolve eq283969 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283969
  have eq284236 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq284110 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq284110
    | (have j0 := eq284110 X0 X1
       grind)
    | exact resolve eq284110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284110
  have eq284488 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq284236 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq284236
    | (have j0 := eq284236 (τ X0) (τ X1)
       grind)
    | exact resolve eq284236 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq284236
  have eq285027 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq284488 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq284488
    | (have j0 := eq284488 X0 X1
       grind)
    | exact resolve eq284488 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284488
  have eq285320 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq285027 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq285027
    | (have j0 := eq285027 X0 X1
       grind)
    | exact resolve eq285027 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285027
  have eq285569 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq285320 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq285320
    | (have j0 := eq285320 X0 X1
       grind)
    | exact resolve eq285320 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285320
  have eq285810 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq285569 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq285569
    | (have j0 := eq285569 X0 X1
       grind)
    | exact resolve eq285569 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285569
  have eq286012 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq285810 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq285810
    | (have j0 := eq285810 X0 X1
       grind)
    | exact resolve eq285810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285810
  have eq286195 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq286012 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq286012
    | (have j0 := eq286012 X0 X1
       grind)
    | exact resolve eq286012 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286012
  have eq286335 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq286195 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq286195
    | (have j0 := eq286195 X0 X1
       grind)
    | exact resolve eq286195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286195
  have eq286459 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq286335 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq286335
    | (have j0 := eq286335 X0 X1
       grind)
    | exact resolve eq286335 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286335
  have eq286666 : ∀ X0 X1 : G, (k (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq286459 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq286459
    | (have j0 := eq286459 (τ X0) X1
       grind)
    | exact resolve eq286459 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq286459
  have eq286940 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq286666 X0 X1
       have j1 := eq3873 X0 X1
       have j2 := eq370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq3873 eq286666
  have eq286952 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq286940 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq286940
    | exact resolve eq286940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286940
  have eq288316 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq286952 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq286952
    | (have j0 := eq286952 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq286952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292069 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq288316 X1 X0
       have i₂ := eq286952 X1 X0
       grind)
    | exact superpose eq286952 eq288316
    | (have j0 := eq288316 X0 X1
       have j1 := eq286952 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq288316 eq286952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286952 eq288316
  have eq295563 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq292069 x y
       grind)
    | exact superpose eq292069 eq16
    | (have j1 := eq292069 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq292069 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq292069 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq292069 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq292069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292069
  have eq295595 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq295563
  have eq295654 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq295595
       grind)
    | exact superpose eq295595 eq10
    | exact resolve eq10 eq295595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295595
  have eq295838 : x = y ∨ x = y := by
    first
    | (have i₁ := eq295654
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq295654
    | exact resolve eq295654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295654
  have eq295839 : x = y := by grind
  clear eq295838
  have eq295842 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq295839
       grind)
    | exact superpose eq295839 eq16
    | exact resolve eq16 eq295839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295839
  have eq295843 : False := by grind
  exact eq295843

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_pyy_pyx_pyy_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq264 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq264 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq264 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq264 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq276 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq265 (σ X0)
       grind)
    | exact superpose eq265 eq15
    | exact resolve eq15 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq265 (τ X0)
       grind)
    | exact superpose eq265 eq31
    | exact resolve eq31 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq282
    | exact resolve eq282 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq295 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq276
    | exact resolve eq276 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq276
  have eq508 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq525 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq508 X0 X1
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq508
    | (have j0 := eq508 X0 X1
       grind)
    | exact resolve eq508 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq652 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq525 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq525
    | exact resolve eq525 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq695 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq652
    | (have j0 := eq652 X0 X1
       grind)
    | exact resolve eq652 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq652
  have eq699 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq695 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq695 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq695 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq695 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq701 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq702 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq701
    | (have j0 := eq701 X0 X1
       grind)
    | exact resolve eq701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq703 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq702
    | exact resolve eq702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq702 (σ X0) X1
       grind)
    | exact superpose eq702 eq15
    | (have j1 := eq702 (σ X0) X1
       grind)
    | exact resolve eq15 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq734 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 X1
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq710
    | (have j0 := eq710 X0 X1
       grind)
    | exact resolve eq710 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq765 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq703 (τ X1) X0
       grind)
    | exact superpose eq703 eq17
    | (have j1 := eq703 (τ X1) X0
       grind)
    | exact resolve eq17 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq703
  have eq910 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq765 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq765
    | exact resolve eq765 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq963 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq910 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq910
    | (have j0 := eq910 X0 X1
       grind)
    | exact resolve eq910 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq2630 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq734 x y
       grind)
    | exact superpose eq734 eq16
    | (have j1 := eq734 x y
       grind)
    | exact resolve eq16 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2648 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq734 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq2683 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2630
       have i₂ := eq963 y x
       grind)
    | exact superpose eq963 eq2630
    | (have j1 := eq963 y x
       grind)
    | (have r₁ := eq2630
       have r₂ := eq963 y x
       grind)
    | exact resolve eq2630 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963 eq2630
  have eq2684 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2683
  have eq2687 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2684
       grind)
    | exact superpose eq2684 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2684
       grind)
    | exact resolve eq13 eq2684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2690 : x = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2687
  have eq2700 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2648 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2648
    | (have j0 := eq2648 (τ X1) (τ X0)
       grind)
    | exact resolve eq2648 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2745 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2700 X0 X1
       have i₂ := eq289 X1
       grind)
    | exact superpose eq289 eq2700
    | (have j0 := eq2700 X0 X1
       grind)
    | exact resolve eq2700 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700
  have eq2765 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2745 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq2745
    | (have j0 := eq2745 X0 X1
       grind)
    | exact resolve eq2745 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2745
  have eq2779 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2765 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2765
    | (have j0 := eq2765 X0 X1
       grind)
    | exact resolve eq2765 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765
  have eq2791 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2779 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2779
    | (have j0 := eq2779 X0 X1
       grind)
    | exact resolve eq2779 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2779
  have eq2798 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2791 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2791
    | (have j0 := eq2791 X0 X1
       grind)
    | exact resolve eq2791 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791
  have eq2804 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X1 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2798 X0 X1
       have i₂ := eq289 X1
       grind)
    | exact superpose eq289 eq2798
    | (have j0 := eq2798 X0 X1
       grind)
    | exact resolve eq2798 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq2798
  have eq2805 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2804 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq2804
    | (have j0 := eq2804 X0 X1
       grind)
    | exact resolve eq2804 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq9216 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2690
       grind)
    | exact superpose eq2690 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2690
       grind)
    | exact resolve eq12 eq2690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2690
  have eq9218 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq9216
  have eq44316 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9218
       grind)
    | exact superpose eq9218 eq16
    | exact resolve eq16 eq9218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9218
  have eq44352 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44316
       have i₂ := eq2684
       grind)
    | exact superpose eq2684 eq44316
    | exact resolve eq44316 eq2684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684 eq44316
  have eq44374 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq44352
  have eq44375 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq44374
  have eq44401 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq44375
       grind)
    | exact superpose eq44375 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq44375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44418 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq44401
       have r₂ := eq295 x
       grind)
    | exact resolve eq44401 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44401
  have eq44421 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq44418
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq44418
    | exact resolve eq44418 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44418
  have eq44422 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq44421
       have i₂ := eq295 x
       grind)
    | exact superpose eq295 eq44421
    | exact resolve eq44421 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq44421
  have eq78138 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq44422
       grind)
    | exact superpose eq44422 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq44422
       grind)
    | exact resolve eq12 eq44422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44422
  have eq78151 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq78138
  have eq78164 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq78151
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq78151
    | exact resolve eq78151 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78151
  have eq856024 : (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq44375
       have i₂ := eq78164
       grind)
    | exact superpose eq78164 eq44375
    | exact resolve eq44375 eq78164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44375 eq78164
  have eq856255 : (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq856024
  have eq856656 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2648 x y
       have i₂ := eq856255
       grind)
    | exact superpose eq856255 eq2648
    | (have j0 := eq2648 x y
       grind)
    | (have r₁ := eq2648 x y
       have r₂ := eq856255
       grind)
    | exact resolve eq2648 eq856255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856659 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2805 y x
       have i₂ := eq856255
       grind)
    | exact superpose eq856255 eq2805
    | (have j0 := eq2805 y x
       grind)
    | (have r₁ := eq2805 y x
       have r₂ := eq856255
       grind)
    | exact resolve eq2805 eq856255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856255
  have eq856884 : (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq856659
  have eq856886 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq856656
  have eq856894 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq2648 x y
       grind)
    | (have r₁ := eq856886
       have r₂ := eq2648 x y
       grind)
    | exact resolve eq856886 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648 eq856886
  have eq856937 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq856894
       grind)
    | exact superpose eq856894 eq16
    | exact resolve eq16 eq856894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856894
  have eq860078 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq856937
       have i₂ := eq856884
       grind)
    | exact superpose eq856884 eq856937
    | exact resolve eq856937 eq856884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856884
  have eq860090 : (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq860078
  have eq860236 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq860090
       grind)
    | exact superpose eq860090 eq10
    | exact resolve eq10 eq860090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860090
  have eq860907 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq860236
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq860236
    | exact resolve eq860236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860236
  have eq861521 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2805 y x
       have i₂ := eq860907
       grind)
    | exact superpose eq860907 eq2805
    | (have j0 := eq2805 y x
       grind)
    | (have r₁ := eq2805 y x
       have r₂ := eq860907
       grind)
    | exact resolve eq2805 eq860907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805 eq860907
  have eq861746 : (M.op x y) = (M.op x x) := by grind
  clear eq861521
  have eq861867 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq856937
       have i₂ := eq861746
       grind)
    | exact superpose eq861746 eq856937
    | exact resolve eq856937 eq861746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856937 eq861746
  have eq861879 : False := by grind
  exact eq861879

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq265 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq266 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq265 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq265
    | (have j0 := eq265 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq265 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5365 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X1) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq266 X0 X1
       grind)
    | exact superpose eq266 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq266 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq266 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X1)
       have r₂ := eq266 X1 X1
       grind)
    | exact resolve eq13 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5367 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) (τ X1)
       have i₂ := eq266 X0 X1
       grind)
    | exact superpose eq266 eq12
    | (have j0 := eq12 (τ X0) (τ X1)
       have j1 := eq266 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq266 X0 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X1)
       have r₂ := eq266 X0 X1
       grind)
    | exact resolve eq12 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq5371 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5367 X0 X1
       have j1 := eq12 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq5367 X0 X0
       have r₂ := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq5367 X0 X1
       have r₂ := eq12 (τ X0) (τ X1)
       grind)
    | exact resolve eq5367 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5367
  have eq5372 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X1) = (k (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5365 X0 X1
       have j1 := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq5365 X0 X1
       have r₂ := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq5365 X1 X1
       have r₂ := eq13 (τ X1) (τ X1)
       grind)
    | exact resolve eq5365 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5365
  have eq5377 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5371 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq5371
    | (have j0 := eq5371 X0 X1
       grind)
    | exact resolve eq5371 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5371
  have eq5378 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5372 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq5372
    | (have j0 := eq5372 X0 X1
       grind)
    | exact resolve eq5372 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5372
  have eq5379 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5378 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5378
  have eq5381 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5377 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5377
    | (have j0 := eq5377 (σ X0) (σ X1)
       grind)
    | exact resolve eq5377 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5377
  have eq5439 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5381 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5381
    | (have j0 := eq5381 X0 X1
       grind)
    | exact resolve eq5381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5381
  have eq5462 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5439 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5439
    | (have j0 := eq5439 X0 X1
       grind)
    | exact resolve eq5439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5439
  have eq5483 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5462 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5462
    | (have j0 := eq5462 X0 X1
       grind)
    | exact resolve eq5462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5462
  have eq5504 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5483 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5483
    | (have j0 := eq5483 X0 X1
       grind)
    | exact resolve eq5483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5483
  have eq5513 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5504 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5504
    | (have j0 := eq5504 X0 X1
       grind)
    | exact resolve eq5504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504
  have eq5522 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5513 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5513
    | (have j0 := eq5513 X0 X1
       grind)
    | exact resolve eq5513 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5513
  have eq5543 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5522 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5522
    | (have j0 := eq5522 (σ X0) (σ X1)
       grind)
    | exact resolve eq5522 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5522
  have eq5567 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5379 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5379
    | (have j0 := eq5379 (σ X0) (σ X1)
       grind)
    | exact resolve eq5379 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5379
  have eq5625 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5567 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5567
    | (have j0 := eq5567 X0 X1
       grind)
    | exact resolve eq5567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5567
  have eq5648 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5625 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5625
    | (have j0 := eq5625 X0 X1
       grind)
    | exact resolve eq5625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5625
  have eq5669 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5648 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5648
    | (have j0 := eq5648 X0 X1
       grind)
    | exact resolve eq5648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5648
  have eq5690 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5669 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5669
    | (have j0 := eq5669 X0 X1
       grind)
    | exact resolve eq5669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5669
  have eq5699 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5690 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5690
    | (have j0 := eq5690 X0 X1
       grind)
    | exact resolve eq5690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5690
  have eq5708 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5699 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5699
    | (have j0 := eq5699 X0 X1
       grind)
    | exact resolve eq5699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5699
  have eq5726 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5708 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5708
    | (have j0 := eq5708 (σ X0) (σ X1)
       grind)
    | exact resolve eq5708 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5708
  have eq12995 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq853 x y
       grind)
    | exact superpose eq853 eq16
    | (have j1 := eq853 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq853 x y
       grind)
    | exact resolve eq16 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq13012 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12995
  have eq13031 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq13012
       grind)
    | exact superpose eq13012 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13012
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13012
       grind)
    | exact resolve eq13 eq13012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13034 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13012
  have eq13035 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13031
  have eq13038 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13035
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq13035
    | exact resolve eq13035 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13035
  have eq13040 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14 eq13038
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq13038 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13038
  have eq13042 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13040
       have r₂ := eq13034
       grind)
    | exact resolve eq13040 eq13034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13034 eq13040
  have eq13049 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq13042
       grind)
    | exact superpose eq13042 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13042
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13042
       grind)
    | exact resolve eq12 eq13042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13042
  have eq13050 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13049
  have eq13053 : (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13050
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq13050
    | exact resolve eq13050 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13050
  have eq13054 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14 eq13053
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq13053 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13053
  have eq13055 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq13054
       grind)
    | exact superpose eq13054 eq10
    | exact resolve eq10 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13054
  have eq13203 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13055
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq13055
    | exact resolve eq13055 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13055
  have eq13204 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13203
  have eq13208 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq13204
       grind)
    | exact superpose eq13204 eq10
    | exact resolve eq10 eq13204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13204
  have eq13355 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13208
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13208
    | exact resolve eq13208 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13208
  have eq13356 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13355
  have eq13362 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq13356
       grind)
    | exact superpose eq13356 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13356
       grind)
    | exact resolve eq13 eq13356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13364 : x ≠ y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq13356
       grind)
    | exact superpose eq13356 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13356
       grind)
    | exact resolve eq12 eq13356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13365 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq13366 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq13362
  have eq13367 : x ≠ y ∨ y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq13364
       have r₂ := eq12 y x
       grind)
    | exact resolve eq13364 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13364
  have eq13368 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13366
       have r₂ := eq13365
       grind)
    | exact resolve eq13366 eq13365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13365 eq13366
  have eq13377 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5543 y x
       have i₂ := eq13368
       grind)
    | exact superpose eq13368 eq5543
    | (have j0 := eq5543 y x
       grind)
    | exact resolve eq5543 eq13368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5543 eq13368
  have eq13388 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq13377
  have eq13406 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13388
       grind)
    | exact superpose eq13388 eq16
    | exact resolve eq16 eq13388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13388
  have eq13415 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13356 eq13406
    | exact resolve eq13406 eq13356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13406
  have eq13416 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq13415
  have eq13420 : x ≠ x ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq13416
       grind)
    | exact superpose eq13416 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13416
       grind)
    | exact resolve eq12 eq13416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13421 : y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq13420
  have eq13432 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5726 y x
       have i₂ := eq13421
       grind)
    | exact superpose eq13421 eq5726
    | (have j0 := eq5726 y x
       grind)
    | exact resolve eq5726 eq13421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5726 eq13421
  have eq13441 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13432
  have eq13442 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq13441
  have eq13453 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13442
       grind)
    | exact superpose eq13442 eq16
    | exact resolve eq16 eq13442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13442
  have eq13459 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13416 eq13453
    | exact resolve eq13453 eq13416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13416 eq13453
  have eq13460 : (σ x) = (σ y) := by grind
  clear eq13459
  have eq13461 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13460
       grind)
    | exact superpose eq13460 eq16
    | exact resolve eq16 eq13460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13462 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13460
       grind)
    | exact superpose eq13460 eq10
    | exact resolve eq10 eq13460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13460
  have eq13609 : x = y := by
    first
    | (have i₁ := eq13462
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13462
    | exact resolve eq13462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13462
  have eq13610 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13356
       have i₂ := eq13609
       grind)
    | exact superpose eq13609 eq13356
    | exact resolve eq13356 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13356
  have eq13613 : x ≠ x ∨ y = (k y x) := by
    first
    | (have i₁ := eq13367
       have i₂ := eq13609
       grind)
    | exact superpose eq13609 eq13367
    | (have r₁ := eq13367
       have r₂ := eq13609
       grind)
    | exact resolve eq13367 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13367
  have eq13615 : y = (k y x) := by grind
  clear eq13613
  have eq13617 : x = (k x x) := by
    first
    | (have i₁ := eq13615
       have i₂ := eq13609
       grind)
    | exact superpose eq13609 eq13615
    | exact resolve eq13615 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13615
  have eq13620 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13610
       have i₂ := eq13609
       grind)
    | exact superpose eq13609 eq13610
    | exact resolve eq13610 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13610
  have eq13621 : x = (M.op x x) := by grind
  clear eq13620
  have eq13633 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq265 x x
       have i₂ := eq13617
       grind)
    | exact superpose eq13617 eq265
    | (have j0 := eq265 x x
       grind)
    | exact resolve eq265 eq13617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq13617
  have eq13652 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq13633
  have eq13655 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq13461
       have i₂ := eq13609
       grind)
    | exact superpose eq13609 eq13461
    | exact resolve eq13461 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13461 eq13609
  have eq13656 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13655
       have i₂ := eq13621
       grind)
    | exact superpose eq13621 eq13655
    | exact resolve eq13655 eq13621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13621 eq13655
  have eq13657 : False := by grind
  exact eq13657

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_x_pxx_pyx_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq47 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op (M.op X4 (M.op X5 X6)) X6) := by
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
  have eq48 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (M.op X4 (M.op (M.op X0 (M.op X1 X2)) X2)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X4 X5 X5
       have i₂ := eq14 X5 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X0)) X5) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq14 X1 X2 (M.op x (M.op x X5)) X5
       have i₂ := eq14 X0 x x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq107 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq108 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq171 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq125
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq171
  have eq236 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) y) = (k X1 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    grind
  have eq259 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X2 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq53 X2 x X3
       have i₂ := eq51 x X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 X2 X4 : G, (M.op X2 X2) = (M.op (M.op (M.op X0 X0) X1) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53 x X2 X4
       have i₂ := eq53 X0 x X1
       grind)
    | (have i₁ := eq53 (M.op X0 X0) X1 x
       have i₂ := eq53 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq294 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X2 ∨ (k (M.op X1 X1) X2) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq53 X0 X1 x
       grind)
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq53 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X0 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) x) X1
       have r₂ := eq53 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq53 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) X2) = (M.op X2 (M.op X1 X1)) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq294 X0 X1 X2
       grind)
    | (have r₁ := eq294 X0 X1 X2
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq294 X1 X0 X2
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq294 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq352 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (M.op X0 X0)
       have i₂ := eq63 X0 (τ X1)
       grind)
    | exact superpose eq63 eq35
    | exact resolve eq35 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X6)) X6) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) X3) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq47 X2 X3 X3 X4 X5 X6
       have i₂ := eq53 X0 X3 X1
       grind)
    | (have i₁ := eq47 X0 (M.op X0 X0) X5 X4 X5 X6
       have i₂ := eq53 X0 X1 X5
       grind)
    | exact superpose eq53 eq47
    | exact resolve eq47 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq682 : ∀ X0 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X2 (M.op (M.op X3 (M.op X4 X5)) X5)) X6) := by
    intro X0 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq48 X3 X4 X5 x X2 X6
       have i₂ := eq51 x X0
       grind)
    | exact superpose eq51 eq48
    | exact resolve eq48 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1155 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X0
       have i₂ := eq54 (σ X0) X1
       grind)
    | (have i₁ := eq78 X0 X0
       have i₂ := eq54 X0 (σ X0)
       grind)
    | exact superpose eq54 eq78
    | exact resolve eq78 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (σ X0)
       have i₂ := eq78 X0 X0
       grind)
    | exact superpose eq78 eq54
    | (have j1 := eq78 X0 X0
       grind)
    | exact resolve eq54 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1179 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1182 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1195 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1155 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1855 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq259 X3 x X5
       have i₂ := eq49 X1 x X0 X2
       grind)
    | (have i₁ := eq259 X0 (M.op X2 (M.op X0 X0)) X3
       have i₂ := eq49 X0 X1 X2 (M.op X2 (M.op X0 X0))
       grind)
    | exact superpose eq49 eq259
    | exact resolve eq259 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq259
  have eq9754 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1195 X1 (M.op X0 X0)
       have i₂ := eq63 X0 (M.op X0 X0)
       grind)
    | exact superpose eq63 eq1195
    | (have j0 := eq1195 X1 (M.op X0 X0)
       grind)
    | exact resolve eq1195 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq9755 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op (M.op X0 X0) X1)) ∨ (M.op X2 X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1195 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq284 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq284 eq1195
    | (have j0 := eq1195 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq1195 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq9757 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 (M.op x y)) y)) ∨ (M.op X1 X1) = (σ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    first
    | exact superpose eq236 eq1195
    | (have j0 := eq1195 X1 (M.op (M.op X0 (M.op x y)) y)
       grind)
    | exact resolve eq1195 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq9871 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1195 X0 (τ X1)
       grind)
    | exact superpose eq1195 eq35
    | (have j1 := eq1195 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9874 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq125
       have i₂ := eq1195 X0 sF0
       grind)
    | exact superpose eq1195 eq125
    | (have j1 := eq1195 X0 (M.op x y)
       grind)
    | exact resolve eq125 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq1195
  have eq9893 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    first
    | (have j0 := eq9757 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9757
  have eq9895 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq9755 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9755
  have eq9896 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9754 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9754
  have eq9904 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq9874
    | (have j0 := eq9874 X0
       grind)
    | exact resolve eq9874 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9874
  have eq9907 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9871 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq9871
    | (have j0 := eq9871 X0 X1
       grind)
    | exact resolve eq9871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9871
  have eq9917 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9907 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq9907
    | (have j0 := eq9907 X0 X1
       grind)
    | exact resolve eq9907 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9907
  have eq10118 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq9896 X1 X0
       grind)
    | exact superpose eq9896 eq16
    | exact resolve eq16 eq9896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10192 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq10118 x X1
       have i₂ := eq50 x X0
       grind)
    | exact superpose eq50 eq10118
    | exact resolve eq10118 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq10195 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10118 x X2
       have i₂ := eq53 X0 x X1
       grind)
    | (have i₁ := eq10118 (M.op X0 X0) X1
       have i₂ := eq53 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq10118
    | exact resolve eq10118 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq10259 : ∀ X0 X1 X3 X4 : G, (M.op X1 X1) = (M.op (M.op (τ (M.op X0 X0)) X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq265 x X3 X1 X4
       have i₂ := eq10118 X0 x
       grind)
    | exact superpose eq10118 eq265
    | exact resolve eq265 eq10118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12840 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (σ (M.op (τ (M.op X0 X0)) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9895 x X3 X1
       have i₂ := eq10118 X0 x
       grind)
    | exact superpose eq10118 eq9895
    | exact resolve eq9895 eq10118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13064 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X1 X1) X2)
       have i₂ := eq9895 X1 X2 X0
       grind)
    | exact superpose eq9895 eq16
    | exact resolve eq16 eq9895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9895
  have eq25984 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op (τ (M.op X0 X0)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq10192 (M.op X1 X1) X1
       have i₂ := eq13064 X0 X1 sF0
       grind)
    | exact superpose eq13064 eq10192
    | exact resolve eq10192 eq13064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10192 eq13064
  have eq26873 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (τ (M.op (τ (M.op X0 X0)) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq10195 x X3 X1
       have i₂ := eq10118 X0 x
       grind)
    | exact superpose eq10118 eq10195
    | exact resolve eq10195 eq10118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10118 eq10195
  have eq31801 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1179 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1179
    | (have j0 := eq1179 (τ X0)
       grind)
    | exact resolve eq1179 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq31816 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq31801 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq31801
    | (have j0 := eq31801 X0
       grind)
    | exact resolve eq31801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31801
  have eq31823 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31816 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq31816
    | (have j0 := eq31816 X0
       grind)
    | exact resolve eq31816 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31816
  have eq31987 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1182 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1182
    | (have j0 := eq1182 (τ X0) X1
       grind)
    | exact resolve eq1182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32067 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1182 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1182
    | (have j0 := eq1182 x X0
       grind)
    | exact resolve eq1182 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32068 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq1182 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1182
    | (have j0 := eq1182 y X0
       grind)
    | exact resolve eq1182 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq32249 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32068 X0
       have i₂ := eq108
       grind)
    | exact superpose eq108 eq32068
    | exact resolve eq32068 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq32068
  have eq32250 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq32067 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq32067
    | exact resolve eq32067 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq32067
  have eq32252 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (σ (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31987 X0 X1
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq31987
    | (have j0 := eq31987 X0 X1
       grind)
    | exact resolve eq31987 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq31987
  have eq32254 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32252 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq32252
    | (have j0 := eq32252 X0 X1
       grind)
    | exact resolve eq32252 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32252
  have eq46707 : ∀ X0 X1 X2 X3 X7 : G, (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X7) := by
    intro X0 X1 X2 X3 X7
    first
    | (have i₁ := eq682 X3 (M.op (M.op x (M.op x x)) x) x x x X7
       have i₂ := eq265 X0 X1 (M.op (M.op x (M.op x x)) x) X2
       grind)
    | (have i₁ := eq682 X0 (M.op (M.op X0 X0) X1) X3 x x x
       have i₂ := eq265 X0 X1 X2 (M.op (M.op X3 (M.op x x)) x)
       grind)
    | exact superpose eq265 eq682
    | exact resolve eq682 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46834 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq682 X4 x x x x x
       have i₂ := eq564 X1 X2 X0 X3 x (M.op x (M.op x x)) x
       grind)
    | (have i₁ := eq682 X0 X2 (M.op X4 X1) X4 X1 X3
       have i₂ := eq564 (M.op X4 X1) X1 X2 X3 X4 x x
       grind)
    | exact superpose eq564 eq682
    | (have j1 := eq564 X1 X2 X0 X3 X4 (σ x) (σ y)
       grind)
    | exact resolve eq682 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq682
  have eq181146 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9917 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9917
  have eq183353 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq32249 eq31823
    | (have j0 := eq31823 (σ y)
       grind)
    | exact resolve eq31823 eq32249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32249
  have eq183369 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq183353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183353
  have eq183466 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq183369 x
       have i₂ := eq9896 X0 x
       grind)
    | exact superpose eq9896 eq183369
    | exact resolve eq183369 eq9896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184502 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq32250 eq31823
    | (have j0 := eq31823 (σ x)
       grind)
    | exact resolve eq31823 eq32250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32250
  have eq184518 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq184502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184502
  have eq184615 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq184518 x
       have i₂ := eq9896 X0 x
       grind)
    | exact superpose eq9896 eq184518
    | exact resolve eq184518 eq9896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184518
  have eq185695 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31823 X1
       have i₂ := eq32254 X1 X0
       grind)
    | exact superpose eq32254 eq31823
    | (have j0 := eq31823 X1
       have j1 := eq32254 X1 X1
       grind)
    | (have r₁ := eq31823 (M.op X1 X1)
       have r₂ := eq32254 (M.op X1 X1) X1
       grind)
    | exact resolve eq31823 eq32254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31823 eq32254
  have eq185823 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq185695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185695
  have eq214156 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq179
       have i₂ := eq9896 sF0 x
       grind)
    | exact superpose eq9896 eq179
    | exact resolve eq179 eq9896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq487855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq487862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq487855
    | exact resolve eq487855 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487855
  have eq487873 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq487862
       have r₂ := eq28
       grind)
    | exact resolve eq487862 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487862
  have eq487875 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq487873
       have i₂ := eq54 sF2 x
       grind)
    | (have i₁ := eq487873
       have i₂ := eq54 X0 sF2
       grind)
    | exact superpose eq54 eq487873
    | exact resolve eq487873 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487873
  have eq489194 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq183466 x
       have i₂ := eq487875 X0
       grind)
    | exact superpose eq487875 eq183466
    | (have j1 := eq487875 X0
       grind)
    | exact resolve eq183466 eq487875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183466 eq487875
  have eq489325 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq489194 X0
       grind)
    | (have r₁ := eq489194 X0
       have r₂ := eq183369 (σ y)
       grind)
    | (have r₁ := eq489194 X0
       have r₂ := eq183369 X0
       grind)
    | exact resolve eq489194 eq183369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183369 eq489194
  have eq489373 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq489325 X0
       grind)
    | (have r₁ := eq489325 X0
       have r₂ := eq25
       grind)
    | exact resolve eq489325 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489325
  have eq489375 : ∀ X0 X1 : G, (σ x) = (M.op X1 X1) ∨ (M.op X0 X0) = (σ y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq489373 X0
       have i₂ := eq54 sF3 X1
       grind)
    | (have i₁ := eq489373 X0
       have i₂ := eq54 X0 sF3
       grind)
    | exact superpose eq54 eq489373
    | (have j0 := eq489373 X1
       grind)
    | exact resolve eq489373 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489373
  have eq491823 : ∀ X0 X2 : G, (M.op X0 X0) = (τ (σ x)) ∨ (σ y) = (M.op X2 X2) ∨ x = (M.op x x) := by
    intro X0 X2
    first
    | (have i₁ := eq26873 x X0 (τ (M.op x x))
       have i₂ := eq489375 X2 (τ (M.op x x))
       grind)
    | (have i₁ := eq26873 X0 x (τ (M.op X0 X0))
       have i₂ := eq489375 (τ (M.op X0 X0)) x
       grind)
    | exact superpose eq489375 eq26873
    | (have j1 := eq489375 X2 x
       grind)
    | exact resolve eq26873 eq489375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489375
  have eq491854 : ∀ X0 X2 : G, (M.op X0 X0) = x ∨ (σ y) = (M.op X2 X2) ∨ x = (M.op x x) := by
    intro X0 X2
    first
    | exact superpose eq29 eq491823
    | (have j0 := eq491823 X0 X2
       grind)
    | exact resolve eq491823 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491823
  have eq492011 : ∀ X2 : G, (σ y) = (M.op X2 X2) ∨ x = (M.op x x) := by
    intro X2
    first
    | (have j0 := eq491854 x X2
       have j1 := eq185823 x x
       grind)
    | (have r₁ := eq491854 x X2
       have r₂ := eq185823 x x
       grind)
    | (have r₁ := eq491854 x x
       have r₂ := eq185823 x (σ y)
       grind)
    | (have r₁ := eq491854 x X2
       have r₂ := eq185823 x x
       grind)
    | exact resolve eq491854 eq185823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491854
  have eq493568 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq26873 x X0 (τ (M.op x x))
       have i₂ := eq492011 (τ (M.op x x))
       grind)
    | exact superpose eq492011 eq26873
    | exact resolve eq26873 eq492011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26873
  have eq493595 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq30 eq493568
    | exact resolve eq493568 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493568
  have eq501750 : ∀ X0 X1 : G, y = (M.op X1 X1) ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq493595 X1
       have i₂ := eq54 x X0
       grind)
    | (have i₁ := eq493595 X1
       have i₂ := eq54 X0 x
       grind)
    | exact superpose eq54 eq493595
    | (have j0 := eq493595 X1
       grind)
    | exact resolve eq493595 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501827 : ∀ X0 X1 : G, (M.op X0 X0) = (σ x) ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9896 x X0
       have i₂ := eq493595 X1
       grind)
    | exact superpose eq493595 eq9896
    | (have j1 := eq493595 X1
       grind)
    | exact resolve eq9896 eq493595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501969 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq184615 x
       have i₂ := eq493595 X0
       grind)
    | exact superpose eq493595 eq184615
    | (have j1 := eq493595 X0
       grind)
    | exact resolve eq184615 eq493595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184615 eq493595
  have eq502088 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq501969 X0
       grind)
    | (have r₁ := eq501969 X0
       have r₂ := eq23
       grind)
    | exact resolve eq501969 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501969
  have eq502130 : ∀ X0 X1 : G, y = (M.op X1 X1) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq501827 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq501827
    | (have j0 := eq501827 X0 X1
       grind)
    | exact resolve eq501827 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501827
  have eq503184 : ∀ X1 : G, y = (σ y) ∨ x = (M.op x x) ∨ x = (M.op X1 X1) := by
    intro X1
    first
    | (have i₁ := eq492011 x
       have i₂ := eq501750 X1 x
       grind)
    | exact superpose eq501750 eq492011
    | (have j1 := eq501750 x X1
       grind)
    | exact resolve eq492011 eq501750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492011 eq501750
  have eq504032 : x = (M.op x x) ∨ y = (σ y) := by
    first
    | (have j0 := eq503184 x
       have j1 := eq185823 x x
       grind)
    | (have r₁ := eq503184 x
       have r₂ := eq185823 x x
       grind)
    | (have r₁ := eq503184 x
       have r₂ := eq185823 x x
       grind)
    | exact resolve eq503184 eq185823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503184
  have eq508249 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq504032
       have i₂ := eq54 x X0
       grind)
    | (have i₁ := eq504032
       have i₂ := eq54 X0 x
       grind)
    | exact superpose eq54 eq504032
    | exact resolve eq504032 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq508327 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9896 x X0
       have i₂ := eq504032
       grind)
    | exact superpose eq504032 eq9896
    | exact resolve eq9896 eq504032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9896 eq504032
  have eq508631 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq508327 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq508327
    | (have j0 := eq508327 X0
       grind)
    | exact resolve eq508327 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508327
  have eq509741 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9893 sF0 x
       have i₂ := eq508249 sF0
       grind)
    | exact superpose eq508249 eq9893
    | exact resolve eq9893 eq508249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9893 eq508249
  have eq510289 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq509741 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq509741
    | (have j0 := eq509741 X0
       grind)
    | exact resolve eq509741 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509741
  have eq510417 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq21 eq510289
    | (have j0 := eq510289 X0
       grind)
    | exact resolve eq510289 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510289
  have eq512456 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq51 X0 sF4
       have i₂ := eq508631 sF4
       grind)
    | exact superpose eq508631 eq51
    | exact resolve eq51 eq508631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq508631
  have eq512968 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq27 eq512456
    | (have j0 := eq512456 X0
       grind)
    | exact resolve eq512456 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512456
  have eq545645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq510417 x
       have i₂ := eq512968 x
       grind)
    | exact superpose eq512968 eq510417
    | exact resolve eq510417 eq512968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510417 eq512968
  have eq546481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq545645
  have eq546494 : y = (σ y) := by
    first
    | (have r₁ := eq546481
       have r₂ := eq28
       grind)
    | exact resolve eq546481 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546481
  have eq546497 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq546494 eq27
    | exact resolve eq27 eq546494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546498 : y = (τ y) := by
    first
    | exact superpose eq546494 eq30
    | exact resolve eq30 eq546494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq546844 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X5) = (M.op (M.op X3 (M.op (σ x) (σ y))) y) := by
    intro X0 X1 X2 X3 X5
    first
    | exact superpose eq546494 eq1855
    | exact resolve eq1855 eq546494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq547851 : ∀ X0 X4 : G, (M.op X0 X0) = (M.op (M.op X4 (M.op (σ x) (σ y))) y) := by
    intro X0 X4
    first
    | (have i₁ := eq546844 (M.op x x) x x X4 x
       have i₂ := eq265 (M.op x x) x X0 x
       grind)
    | (have i₁ := eq546844 X0 x x x (M.op (M.op X0 (M.op x x)) x)
       have i₂ := eq265 X0 x (M.op (M.op X0 (M.op x x)) x) X4
       grind)
    | exact superpose eq265 eq546844
    | exact resolve eq546844 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq546844
  have eq665090 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op (τ (σ x)) y)) ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25984 X0 X1
       have i₂ := eq502088 X0
       grind)
    | exact superpose eq502088 eq25984
    | (have j1 := eq502088 X1
       grind)
    | exact resolve eq25984 eq502088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25984 eq502088
  have eq665302 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op x y)) ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | exact superpose eq29 eq665090
    | (have j0 := eq665090 X0 X1
       grind)
    | exact resolve eq665090 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665090
  have eq665357 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op x y)) ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq665302 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq665302
    | (have j0 := eq665302 X0 X1
       grind)
    | exact resolve eq665302 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665302
  have eq665756 : ∀ X0 X1 : G, (σ x) = (M.op X1 X1) ∨ y = (k X0 y) := by
    intro X0 X1
    grind
  clear eq502130
  have eq670247 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) y) ∨ y = (k X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq547851 X0 sF4
       have i₂ := eq665756 X0 sF4
       grind)
    | exact superpose eq665756 eq547851
    | (have j1 := eq665756 X1 X1
       grind)
    | exact resolve eq547851 eq665756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547851 eq665756
  have eq670770 : ∀ X0 X1 : G, y = (k X1 y) ∨ (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq546497 eq670247
    | (have j0 := eq670247 X0 X1
       grind)
    | exact resolve eq670247 eq546497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670247
  have eq671894 : ∀ X0 X1 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (M.op (σ x) (σ y)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq181146 X0 y
       have i₂ := eq670770 X1 y
       grind)
    | exact superpose eq670770 eq181146
    | (have j0 := eq181146 X0 y
       have j1 := eq670770 X1 X1
       grind)
    | (have r₁ := eq181146 X0 y
       have r₂ := eq670770 X0 y
       grind)
    | exact resolve eq181146 eq670770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181146 eq670770
  have eq671976 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X1 X1) ∨ (M.op X0 X0) = y := by
    intro X0 X1
    first
    | (have j0 := eq671894 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671894
  have eq673446 : ∀ X1 : G, (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op X1 X1) := by
    intro X1
    first
    | (have i₁ := eq9904 X1
       have i₂ := eq671976 x X1
       grind)
    | (have i₁ := eq9904 x
       have i₂ := eq671976 x X1
       grind)
    | exact superpose eq671976 eq9904
    | (have j1 := eq671976 X1 X1
       grind)
    | exact resolve eq9904 eq671976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9904
  have eq674705 : ∀ X0 : G, y ≠ (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq671976 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671976
  have eq674890 : ∀ X1 : G, (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op X1 X1) := by
    intro X1
    first
    | (have j0 := eq673446 X1
       grind)
    | (have r₁ := eq673446 X1
       have r₂ := eq28
       grind)
    | exact resolve eq673446 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673446
  have eq831215 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (τ (M.op x y))) ∨ y = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq12840 x X0 (τ (M.op x x))
       have i₂ := eq665357 (τ (M.op x x)) X2
       grind)
    | (have i₁ := eq12840 X0 x (τ (M.op X0 X0))
       have i₂ := eq665357 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq665357 eq12840
    | (have j1 := eq665357 X0 X2
       grind)
    | exact resolve eq12840 eq665357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12840 eq665357
  have eq831293 : ∀ X0 X2 : G, y = (M.op X2 X2) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq831215 X0 X2
       have i₂ := eq15 sF0
       grind)
    | exact superpose eq15 eq831215
    | (have j0 := eq831215 X0 X2
       grind)
    | exact resolve eq831215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831215
  have eq832634 : ∀ X1 : G, y = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op X1 X1) := by
    intro X1
    first
    | (have i₁ := eq214156 x
       have i₂ := eq831293 X1 x
       grind)
    | exact superpose eq831293 eq214156
    | (have j1 := eq831293 (M.op x y) x
       grind)
    | exact resolve eq214156 eq831293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214156 eq831293
  have eq833893 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j0 := eq832634 (M.op x y)
       have j1 := eq185823 x (M.op x y)
       grind)
    | (have r₁ := eq832634 x
       have r₂ := eq185823 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq832634 x
       have r₂ := eq185823 x (M.op x y)
       grind)
    | exact resolve eq832634 eq185823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185823 eq832634
  have eq840032 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ y = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq833893 eq352
    | exact resolve eq352 eq833893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq833893
  have eq840518 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ y = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq840032
    | (have j0 := eq840032 X0
       grind)
    | exact resolve eq840032 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840032
  have eq845046 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq674890 eq840518
    | (have j1 := eq674890 X0
       grind)
    | exact resolve eq840518 eq674890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674890 eq840518
  have eq845212 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq845046 X0
       have j1 := eq674705 X0
       grind)
    | (have r₁ := eq845046 X0
       have r₂ := eq674705 X0
       grind)
    | exact resolve eq845046 eq674705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674705 eq845046
  have eq845223 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq845212 X0
       grind)
    | (have r₁ := eq845212 X0
       have r₂ := eq28
       grind)
    | exact resolve eq845212 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845212
  have eq847099 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op y X2) := by
    intro X0 X2
    first
    | (have i₁ := eq10259 x X0 (τ (M.op x x)) X2
       have i₂ := eq845223 (τ (M.op x x))
       grind)
    | exact superpose eq845223 eq10259
    | exact resolve eq10259 eq845223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10259
  have eq847177 : ∀ X2 : G, y = (M.op y X2) := by
    intro X2
    first
    | (have i₁ := eq847099 x X2
       have i₂ := eq845223 x
       grind)
    | exact superpose eq845223 eq847099
    | exact resolve eq847099 eq845223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847099
  have eq864650 : ∀ X1 X2 X3 X7 : G, (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op y X1) X2) X7) := by
    intro X1 X2 X3 X7
    first
    | (have i₁ := eq46707 x X1 X2 X3 X7
       have i₂ := eq845223 x
       grind)
    | exact superpose eq845223 eq46707
    | exact resolve eq46707 eq845223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46707
  have eq864651 : ∀ X2 X3 X7 : G, (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op y X2) X7) := by
    intro X2 X3 X7
    first
    | (have i₁ := eq864650 x X2 X3 X7
       have i₂ := eq847177 x
       grind)
    | exact superpose eq847177 eq864650
    | exact resolve eq864650 eq847177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864650
  have eq864652 : ∀ X3 X7 : G, (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) = (M.op y X7) := by
    intro X3 X7
    first
    | (have i₁ := eq864651 x X3 X7
       have i₂ := eq847177 x
       grind)
    | exact superpose eq847177 eq864651
    | exact resolve eq864651 eq847177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864651
  have eq864653 : ∀ X3 : G, y = (M.op (M.op X3 (M.op (σ x) (σ y))) (σ y)) := by
    intro X3
    first
    | (have i₁ := eq864652 X3 x
       have i₂ := eq847177 x
       grind)
    | exact superpose eq847177 eq864652
    | exact resolve eq864652 eq847177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864652
  have eq864654 : ∀ X3 : G, y = (M.op (M.op X3 (M.op (σ x) (σ y))) y) := by
    intro X3
    first
    | exact superpose eq546494 eq864653
    | exact resolve eq864653 eq546494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864653
  have eq866106 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X4 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X0 (M.op y X2)) X3) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq46834 X0 x X2 X3 X4
       have i₂ := eq845223 x
       grind)
    | exact superpose eq845223 eq46834
    | exact resolve eq46834 eq845223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46834
  have eq866107 : ∀ X0 X3 X4 : G, (M.op (M.op X4 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X0 y) X3) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq866106 X0 x X3 X4
       have i₂ := eq847177 x
       grind)
    | exact superpose eq847177 eq866106
    | exact resolve eq866106 eq847177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847177 eq866106
  have eq866108 : ∀ X0 X3 X4 : G, (M.op (M.op X0 y) X3) = (M.op (M.op X4 (M.op (σ x) (σ y))) y) := by
    intro X0 X3 X4
    first
    | exact superpose eq546494 eq866107
    | exact resolve eq866107 eq546494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866107
  have eq866109 : ∀ X0 X3 : G, y = (M.op (M.op X0 y) X3) := by
    intro X0 X3
    first
    | exact superpose eq864654 eq866108
    | exact resolve eq866108 eq864654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864654 eq866108
  have eq867062 : ∀ X1 X2 : G, (M.op X1 y) = (k y X1) ∨ (M.op X2 X2) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq305 x (M.op x y) X2
       have i₂ := eq866109 x (M.op x y)
       grind)
    | exact superpose eq866109 eq305
    | (have j0 := eq305 X2 X1 X1
       grind)
    | exact resolve eq305 eq866109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq866109
  have eq868976 : ∀ X1 : G, (M.op X1 y) = (k y X1) ∨ y = X1 := by
    intro X1
    first
    | (have i₁ := eq867062 X1 x
       have i₂ := eq845223 x
       grind)
    | exact superpose eq845223 eq867062
    | (have j0 := eq867062 X1 x
       grind)
    | exact resolve eq867062 eq845223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867062
  have eq920213 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq868976 x
       grind)
    | exact superpose eq868976 eq107
    | (have j1 := eq868976 x
       grind)
    | exact resolve eq107 eq868976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq920376 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq546494 eq920213
    | exact resolve eq920213 eq546494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920213
  have eq920465 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq920376
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq920376
    | exact resolve eq920376 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920376
  have eq920527 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq920465
    | exact resolve eq920465 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920465
  have eq920570 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq920527 eq868976
    | (have j0 := eq868976 (σ x)
       grind)
    | exact resolve eq868976 eq920527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868976 eq920527
  have eq920589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq546497 eq920570
    | exact resolve eq920570 eq546497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546497 eq920570
  have eq920599 : y = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq920589
       have r₂ := eq28
       grind)
    | exact resolve eq920589 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920589
  have eq920608 : x = (τ y) ∨ x = y := by
    first
    | exact superpose eq920599 eq29
    | exact resolve eq29 eq920599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq920599
  have eq920842 : x = y ∨ x = y := by
    first
    | (have i₁ := eq920608
       have i₂ := eq546498
       grind)
    | exact superpose eq546498 eq920608
    | exact resolve eq920608 eq546498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546498 eq920608
  have eq920843 : x = y := by grind
  clear eq920842
  have eq920957 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq920843
       grind)
    | exact superpose eq920843 eq19
    | exact resolve eq19 eq920843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920958 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq920843
       grind)
    | exact superpose eq920843 eq25
    | exact resolve eq25 eq920843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq921503 : y = (σ x) := by
    first
    | exact superpose eq546494 eq920958
    | exact resolve eq920958 eq546494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920958
  have eq921504 : y = (M.op x y) := by
    first
    | (have i₁ := eq920957
       have i₂ := eq845223 x
       grind)
    | exact superpose eq845223 eq920957
    | exact resolve eq920957 eq845223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845223 eq920957
  have eq921693 : y = (σ x) := by
    first
    | (have i₁ := eq921503
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq921503
    | exact resolve eq921503 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921503
  have eq921694 : x = (M.op x y) := by
    first
    | (have i₁ := eq921504
       have i₂ := eq920843
       grind)
    | exact superpose eq920843 eq921504
    | exact resolve eq921504 eq920843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921504
  have eq921827 : x = (σ x) := by
    first
    | (have i₁ := eq921693
       have i₂ := eq920843
       grind)
    | exact superpose eq920843 eq921693
    | exact resolve eq921693 eq920843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920843 eq921693
  have eq921977 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq921694 eq21
    | exact resolve eq21 eq921694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq922333 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq921977
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq921977
    | exact resolve eq921977 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq921977
  have eq922777 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq921827 eq27
    | exact resolve eq27 eq921827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq922971 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq546494 eq922777
    | exact resolve eq922777 eq546494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546494 eq922777
  have eq923028 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq922971
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq922971
    | exact resolve eq922971 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq922971
  have eq923070 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq921694 eq923028
    | exact resolve eq923028 eq921694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921694 eq923028
  have eq923126 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq921827 eq922333
    | exact resolve eq922333 eq921827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921827 eq922333
  have eq923127 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq923070 eq28
    | exact resolve eq28 eq923070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq923070
  have eq924159 : False := by grind
  exact eq924159

/-- `Equation3926`: `x ◇ y = (x ◇ (y ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_x_y_pyx_Equation3926 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3926 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3926.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X0)) X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq64 X0 X1 X2
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq444 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 X0 x
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq485 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X0 x
       have i₂ := eq457 X0
       grind)
    | exact superpose eq457 eq64
    | (have j1 := eq457 X0
       grind)
    | exact resolve eq64 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq514 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq485 (σ X0) X1
       grind)
    | exact superpose eq485 eq15
    | (have j1 := eq485 (σ X0) X1
       grind)
    | exact resolve eq15 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq750 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = X0 ∨ (M.op X0 X3) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X1 X0 X3
       have i₂ := eq444 X0 X1 X2
       grind)
    | exact superpose eq444 eq64
    | (have j1 := eq444 X0 X1 X2
       grind)
    | exact resolve eq64 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq3595 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq514 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq3649 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3595 (M.op X0 X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq3595
    | (have j0 := eq3595 (M.op X0 X1)
       grind)
    | exact resolve eq3595 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3657 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3595 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq3595
    | (have j0 := eq3595 (τ X0)
       grind)
    | exact resolve eq3595 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3595
  have eq3661 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3649
  have eq3670 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3657 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3657
    | (have j0 := eq3657 X0
       grind)
    | exact resolve eq3657 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3657
  have eq3673 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3670 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3670
    | (have j0 := eq3670 X0
       grind)
    | exact resolve eq3670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670
  have eq3690 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3673 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq3673
    | (have j0 := eq3673 (τ X0)
       grind)
    | exact resolve eq3673 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3673
  have eq3729 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq3661 X0 X1
       grind)
    | exact superpose eq3661 eq64
    | exact resolve eq64 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq4156 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3690 (M.op X0 X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq3690
    | (have j0 := eq3690 (M.op X0 X1)
       grind)
    | exact resolve eq3690 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq3690
  have eq4173 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4156 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4156
  have eq4224 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
       have i₂ := eq4173 X0 X1
       grind)
    | exact superpose eq4173 eq64
    | exact resolve eq64 eq4173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq4173
  have eq10603 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq750 X0 X2 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq10604 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq10603 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10603
  have eq10652 : ∀ X0 X2 X3 : G, (σ X0) = (M.op (σ X0) X2) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3729 X0 x X2
       have i₂ := eq10604 X0 x X2
       grind)
    | exact superpose eq10604 eq3729
    | (have j1 := eq10604 (σ X0) X2 X2
       grind)
    | exact resolve eq3729 eq10604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10658 : ∀ X0 X2 X3 : G, (τ X0) = (M.op (τ X0) X2) ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq4224 X0 x X2
       have i₂ := eq10604 X0 x X2
       grind)
    | exact superpose eq10604 eq4224
    | (have j1 := eq10604 (τ X0) X2 X2
       grind)
    | exact resolve eq4224 eq10604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4224
  have eq13875 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq10652 x (σ y) X0
       grind)
    | exact superpose eq10652 eq16
    | (have j1 := eq10652 x x X0
       grind)
    | exact resolve eq16 eq10652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10652
  have eq14513 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 x) = (M.op x X0) ∨ (M.op x X1) = (k X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq13875 X0
       have i₂ := eq10604 x y X1
       grind)
    | exact superpose eq10604 eq13875
    | (have j0 := eq13875 X0
       have j1 := eq10604 x X1 X0
       grind)
    | exact resolve eq13875 eq10604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10604 eq13875
  have eq14516 : ∀ X0 X1 : G, (k X0 x) = (M.op x X0) ∨ (M.op x X1) = (k X1 x) := by
    intro X0 X1
    first
    | (have j0 := eq14513 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14513
  have eq14526 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (k X2 (σ X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10658 (σ X0) X2 x
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10658
    | (have j0 := eq10658 (σ X0) X2 X2
       grind)
    | exact resolve eq10658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10658
  have eq14826 : ∀ X0 : G, (M.op x X0) ≠ (M.op x X0) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq14516 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14516
  have eq14827 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq14826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14826
  have eq16399 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14526 X0 X2 (σ X1)
       grind)
    | exact superpose eq14526 eq15
    | (have j1 := eq14526 X0 X2 X2
       grind)
    | exact resolve eq15 eq14526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14526
  have eq19816 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq16399 x y X0
       grind)
    | exact superpose eq16399 eq16
    | (have j1 := eq16399 x x X0
       grind)
    | exact resolve eq16 eq16399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16399
  have eq19972 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq19816 X0
       have i₂ := eq14827 y
       grind)
    | exact superpose eq14827 eq19816
    | (have j0 := eq19816 X0
       grind)
    | exact resolve eq19816 eq14827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14827 eq19816
  have eq19973 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq19972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19972
  have eq20130 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq3729 x x x
       have i₂ := eq19973 x
       grind)
    | exact superpose eq19973 eq3729
    | exact resolve eq3729 eq19973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729
  have eq20692 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20130 (σ y)
       grind)
    | exact superpose eq20130 eq16
    | exact resolve eq16 eq20130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20130
  have eq20799 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq20692
       have i₂ := eq19973 y
       grind)
    | exact superpose eq19973 eq20692
    | exact resolve eq20692 eq19973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19973 eq20692
  have eq20800 : False := by grind
  exact eq20800

/-- `Equation3958`: `x ◇ y = (y ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_x_pyx_Equation3958 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3958 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3958.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X0 X2)) X1) := by
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
  have eq53 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) X3) = (M.op (M.op X3 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 X3
       have i₂ := eq14 X0 X3 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq94 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq90
  have eq95 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq118 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq121 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq118
  have eq122 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq121
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X1 (M.op (σ x) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq224 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq221 x X1
       have i₂ := eq14 sF2 X1 x
       grind)
    | exact superpose eq14 eq221
    | exact resolve eq221 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq238 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq249 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq238 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq238
    | exact resolve eq238 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq250 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq249
  have eq625 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq16
    | exact resolve eq16 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq745 : ∀ X0 X1 X2 : G, (M.op (τ X0) X2) = (M.op (M.op X1 (τ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (τ X0) X1 (τ X0) X2
       have i₂ := eq625 X0
       grind)
    | exact superpose eq625 eq57
    | exact resolve eq57 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq16797 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq103
       grind)
    | exact resolve eq12 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq16807 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq16797
  have eq16808 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = y := by grind
  clear eq16807
  have eq16824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq16808 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq16808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16808
  have eq16825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq27 eq16824
    | exact resolve eq16824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16824
  have eq16836 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq16825
       have r₂ := eq28
       grind)
    | exact resolve eq16825 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16825
  have eq16840 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq16836 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16836
       grind)
    | exact resolve eq12 eq16836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16836
  have eq16850 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = y := by grind
  clear eq16840
  have eq16851 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq16850
  have eq16858 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq16851 eq101
    | exact resolve eq101 eq16851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq16851
  have eq16880 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq16858
    | exact resolve eq16858 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16858
  have eq16881 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16880
  have eq16887 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq16881
       grind)
    | exact superpose eq16881 eq89
    | exact resolve eq89 eq16881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq16899 : y = (M.op x y) ∨ (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq16881
       grind)
    | exact superpose eq16881 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq16881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16881
  have eq16900 : y = (M.op x y) ∨ (M.op x x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16899
  have eq16902 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16900
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16900
    | exact resolve eq16900 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16900
  have eq16914 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16887
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16887
    | exact resolve eq16887 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16887
  have eq16960 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16914 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq16914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16914
  have eq16961 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16960
  have eq16965 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq16961
    | exact resolve eq16961 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16961
  have eq17737 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op x x)) X1) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq57 y X0 x X1
       have i₂ := eq16902
       grind)
    | exact superpose eq16902 eq57
    | exact resolve eq57 eq16902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16902
  have eq17747 : ∀ X1 : G, (M.op x X1) = (M.op y X1) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq17737 x X1
       have i₂ := eq57 x x x X1
       grind)
    | exact superpose eq57 eq17737
    | exact resolve eq17737 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17737
  have eq17752 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op X0 (M.op (σ x) (σ x))) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq16965 eq57
    | exact resolve eq57 eq16965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16965
  have eq17762 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (σ y) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq17752 X1 x
       have i₂ := eq57 sF2 X1 sF2 x
       grind)
    | exact superpose eq57 eq17752
    | exact resolve eq17752 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17752
  have eq17764 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq17747 y
       grind)
    | exact superpose eq17747 eq95
    | exact resolve eq95 eq17747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17747
  have eq17826 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17764
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17764
    | exact resolve eq17764 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17764
  have eq17837 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17826
    | exact resolve eq17826 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17826
  have eq18205 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17762 eq128
    | exact resolve eq128 eq17762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq18212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17762 eq17837
    | exact resolve eq17837 eq17762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17762
  have eq18250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18212
  have eq18262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18250
    | exact resolve eq18250 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18250
  have eq18269 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq18205
    | exact resolve eq18205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18205
  have eq18274 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18262
       have r₂ := eq28
       grind)
    | exact resolve eq18262 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18262
  have eq18277 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ y)) X1) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq18274 eq224
    | exact resolve eq224 eq18274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq18560 : (M.op (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq18269
       grind)
    | exact superpose eq18269 eq95
    | exact resolve eq95 eq18269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18269
  have eq18602 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18560
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq18560
    | exact resolve eq18560 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18560
  have eq31634 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27 eq18277
    | (have j0 := eq18277 (σ x) X0
       grind)
    | exact resolve eq18277 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18277
  have eq31714 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18274 eq31634
    | exact resolve eq31634 eq18274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18274 eq31634
  have eq31771 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31714 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31714
  have eq32181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31771 eq17837
    | exact resolve eq17837 eq31771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17837 eq31771
  have eq32246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq32181
  have eq32272 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq32246
    | exact resolve eq32246 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32246
  have eq32290 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq32272
       have r₂ := eq28
       grind)
    | exact resolve eq32272 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32272
  have eq32589 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq32290 eq30
    | exact resolve eq30 eq32290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32290
  have eq32713 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq32589
    | exact resolve eq32589 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32589
  have eq32714 : y = (M.op x y) ∨ x = y := by grind
  clear eq32713
  have eq32733 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq32714 eq21
    | exact resolve eq21 eq32714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32735 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq32714 eq53
    | exact resolve eq53 eq32714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq32750 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) ∨ x = y := by
    first
    | exact superpose eq32714 eq122
    | exact resolve eq122 eq32714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq32890 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq32750
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq32750
    | exact resolve eq32750 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32750
  have eq32906 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq32733
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32733
    | exact resolve eq32733 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32733
  have eq33018 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq32906 eq18602
    | exact resolve eq18602 eq32906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18602 eq32906
  have eq33075 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq33018
  have eq33103 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq33075
       have r₂ := eq28
       grind)
    | exact resolve eq33075 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33075
  have eq33535 : ∀ X0 X1 : G, (M.op (τ (σ y)) X0) = (M.op (M.op X1 (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) X0) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq32890 eq745
    | exact resolve eq745 eq32890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33574 : ∀ X0 : G, (M.op (τ (σ (M.op x y))) X0) = (M.op (τ (σ y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq33535 x x
       have i₂ := eq745 sF1 x x
       grind)
    | exact superpose eq745 eq33535
    | exact resolve eq33535 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq33535
  have eq33591 : ∀ X0 : G, (M.op (τ (σ (M.op x y))) X0) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30 eq33574
    | exact resolve eq33574 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq33574
  have eq33592 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq31 eq33591
    | exact resolve eq33591 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33591
  have eq42258 : (M.op x x) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq32735 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32735
    | (have j0 := eq32735 x
       grind)
    | exact resolve eq32735 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32735
  have eq42349 : (M.op x x) = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq42258 eq33592
    | exact resolve eq33592 eq42258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33592 eq42258
  have eq42362 : (M.op x x) = (M.op y x) ∨ x = y := by grind
  clear eq42349
  have eq42675 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op x x)) X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq57 y X0 x X1
       have i₂ := eq42362
       grind)
    | exact superpose eq42362 eq57
    | exact resolve eq57 eq42362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42362
  have eq42687 : ∀ X1 : G, (M.op x X1) = (M.op y X1) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq42675 x X1
       have i₂ := eq57 x x x X1
       grind)
    | exact superpose eq57 eq42675
    | exact resolve eq42675 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq42675
  have eq43091 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq42687 y
       grind)
    | exact superpose eq42687 eq95
    | exact resolve eq95 eq42687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq42687
  have eq43213 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq43091
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq43091
    | exact resolve eq43091 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43091
  have eq43231 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq43213
    | exact resolve eq43213 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43213
  have eq43571 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq43231 eq32890
    | exact resolve eq32890 eq43231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32890 eq43231
  have eq43603 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq43571
  have eq44431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq43603 eq33103
    | exact resolve eq33103 eq43603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33103 eq43603
  have eq44454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq44431
  have eq44457 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq44454
       have r₂ := eq28
       grind)
    | exact resolve eq44454 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44454
  have eq44472 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq44457 eq29
    | exact resolve eq29 eq44457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44457
  have eq44703 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq44472
    | exact resolve eq44472 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq44472
  have eq45136 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq44703 eq32714
    | exact resolve eq32714 eq44703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32714 eq44703
  have eq45165 : x = y := by grind
  clear eq45136
  have eq45294 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq45165
       grind)
    | exact superpose eq45165 eq19
    | exact resolve eq19 eq45165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq45295 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq45165
       grind)
    | exact superpose eq45165 eq25
    | exact resolve eq25 eq45165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq45165
  have eq45484 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq45295
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45295
    | exact resolve eq45295 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq45295
  have eq45508 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq45484 eq27
    | exact resolve eq27 eq45484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq45484
  have eq45748 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq45508 eq69
    | exact resolve eq69 eq45508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq45508
  have eq45787 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq45748
       have i₂ := eq45294
       grind)
    | exact superpose eq45294 eq45748
    | exact resolve eq45748 eq45294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45294 eq45748
  have eq45797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45787 eq15
    | exact resolve eq15 eq45787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45787
  have eq45958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq45797
    | exact resolve eq45797 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq45797
  have eq46007 : False := by grind
  exact eq46007

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation3997 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq288 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq89 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq89 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq291 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq288 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq292 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq292
    | (have j0 := eq292 X0 X1
       grind)
    | exact resolve eq292 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq302 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       have j1 := eq290 X1 X0
       grind)
    | (have r₁ := eq297 X1 X0
       have r₂ := eq290 X0 X1
       grind)
    | (have r₁ := eq297 (k X1 X0) X1
       have r₂ := eq290 X0 X1
       grind)
    | (have r₁ := eq297 X1 X1
       have r₂ := eq290 X1 X1
       grind)
    | exact resolve eq297 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq297
  have eq622 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq302 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302
    | exact resolve eq302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq302 y x
       grind)
    | exact superpose eq302 eq16
    | (have j1 := eq302 y x
       grind)
    | exact resolve eq16 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq653 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq622
    | (have j0 := eq622 X0 X1
       grind)
    | exact resolve eq622 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq622
  have eq654 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq653
    | exact resolve eq653 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq717 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq654 (τ X1) X0
       grind)
    | exact superpose eq654 eq18
    | (have j1 := eq654 (τ X1) X0
       grind)
    | exact resolve eq18 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq654
  have eq928 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq717 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq717
    | exact resolve eq717 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq979 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq928 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq928
    | (have j0 := eq928 X0 X1
       grind)
    | exact resolve eq928 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1158 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq636
       have i₂ := eq979 y x
       grind)
    | exact superpose eq979 eq636
    | (have j1 := eq979 (σ y) (σ x)
       grind)
    | (have r₁ := eq636
       have r₂ := eq979 y x
       grind)
    | exact resolve eq636 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1158
  have eq1184 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1159
  have eq1197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq636
       have i₂ := eq1184
       grind)
    | exact superpose eq1184 eq636
    | exact resolve eq636 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq1184
  have eq1198 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1197
  have eq1199 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1198
  have eq1257 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1199
  have eq1271 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1257
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1257
    | exact resolve eq1257 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1276 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1271
       grind)
    | exact superpose eq1271 eq16
    | exact resolve eq16 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1346 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1276
       have i₂ := eq979 y x
       grind)
    | exact superpose eq979 eq1276
    | (have j1 := eq979 y x
       grind)
    | (have r₁ := eq1276
       have r₂ := eq979 y x
       grind)
    | exact resolve eq1276 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1347 : y = (M.op x x) := by grind
  clear eq1346
  have eq1353 : (M.op x y) = (k y x) := by grind
  clear eq1347
  have eq1408 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1276
       have i₂ := eq1353
       grind)
    | exact superpose eq1353 eq1276
    | exact resolve eq1276 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276 eq1353
  have eq1411 : False := by grind
  exact eq1411
