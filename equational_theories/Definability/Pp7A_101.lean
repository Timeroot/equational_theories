import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq15
    | exact resolve eq15 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq51 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq12
    | exact resolve eq12 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53 x y
       grind)
    | exact superpose eq53 eq16
    | (have j1 := eq53 x y
       grind)
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq821 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq871 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq821 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq821
    | (have j0 := eq821 X0 X1
       grind)
    | exact resolve eq821 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq1251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq134
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq134
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq134
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq134
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq134 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq1252 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq1251
  have eq15565 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1252
       grind)
    | exact superpose eq1252 eq16
    | exact resolve eq16 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq15566 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq15565
       have r₂ := eq35 x
       grind)
    | exact resolve eq15565 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15565
  have eq15598 : y = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15566
       grind)
    | exact superpose eq15566 eq10
    | exact resolve eq10 eq15566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15566
  have eq15682 : x = y ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq15598
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15598
    | exact resolve eq15598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15598
  have eq15924 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15682
       grind)
    | exact superpose eq15682 eq16
    | exact resolve eq16 eq15682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15682
  have eq15925 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq15924
       have r₂ := eq35 x
       grind)
    | exact resolve eq15924 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15924
  have eq15928 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15925
       grind)
    | exact superpose eq15925 eq16
    | exact resolve eq16 eq15925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15939 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq76 y (σ x)
       have i₂ := eq15925
       grind)
    | exact superpose eq15925 eq76
    | (have j0 := eq76 y (σ x)
       grind)
    | (have r₁ := eq76 y (σ x)
       have r₂ := eq15925
       grind)
    | exact resolve eq76 eq15925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq15925
  have eq15993 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq15939
  have eq16008 : (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq15993
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq15993
    | exact resolve eq15993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15993
  have eq16175 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq871 x y
       have i₂ := eq16008
       grind)
    | exact superpose eq16008 eq871
    | (have j0 := eq871 x y
       grind)
    | exact resolve eq871 eq16008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq16176 : (k x y) = (τ (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq16008
       grind)
    | exact superpose eq16008 eq10
    | exact resolve eq10 eq16008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16008
  have eq16243 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq16175
  have eq16266 : (k x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16176
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq16176
    | exact resolve eq16176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16176
  have eq16267 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq16243
       have r₂ := eq15928
       grind)
    | exact resolve eq16243 eq15928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15928 eq16243
  have eq16270 : (k x y) = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq16266
       have r₂ := eq12 x y
       grind)
    | exact resolve eq16266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16266
  have eq16425 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq142 x y
       have i₂ := eq16270
       grind)
    | exact superpose eq16270 eq142
    | (have j0 := eq142 x y
       grind)
    | exact resolve eq142 eq16270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq16270
  have eq16433 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq16425
  have eq16436 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16267
       grind)
    | exact superpose eq16267 eq16
    | exact resolve eq16 eq16267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16267
  have eq16438 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq16436
       have r₂ := eq35 x
       grind)
    | exact resolve eq16436 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16436
  have eq19104 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16433
       grind)
    | exact superpose eq16433 eq16
    | exact resolve eq16 eq16433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16433
  have eq19247 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19104
       have i₂ := eq16438
       grind)
    | exact superpose eq16438 eq19104
    | exact resolve eq19104 eq16438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16438 eq19104
  have eq19248 : (σ x) = (σ y) := by grind
  clear eq19247
  have eq19264 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19248
       grind)
    | exact superpose eq19248 eq16
    | exact resolve eq16 eq19248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19269 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19248
       grind)
    | exact superpose eq19248 eq10
    | exact resolve eq10 eq19248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19248
  have eq19397 : x = y := by
    first
    | (have i₁ := eq19269
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19269
    | exact resolve eq19269 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19269
  have eq19398 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq19264
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq19264
    | exact resolve eq19264 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq19264
  have eq19403 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq19398
       have i₂ := eq19397
       grind)
    | exact superpose eq19397 eq19398
    | exact resolve eq19398 eq19397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19397 eq19398
  have eq19404 : False := by grind
  exact eq19404

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pxy_pxx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq49 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq49 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq50 (σ X0)
       grind)
    | exact superpose eq50 eq15
    | exact resolve eq15 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq50 (τ X0)
       grind)
    | exact superpose eq50 eq18
    | exact resolve eq18 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq57
    | exact resolve eq57 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq57
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq292 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq328 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq292
    | (have j0 := eq292 X0 X1
       grind)
    | exact resolve eq292 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq292
  have eq333 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq328 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq328 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq328 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq328 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq336 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq333 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq333
    | (have j0 := eq333 X0 X1
       grind)
    | exact resolve eq333 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq333
  have eq887 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq336
    | exact resolve eq336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq336 (σ X0) X1
       grind)
    | exact superpose eq336 eq15
    | (have j1 := eq336 (σ X0) X1
       grind)
    | exact resolve eq15 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq918 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq899 X0 X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq899
    | (have j0 := eq899 X0 X1
       grind)
    | exact resolve eq899 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq936 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq887 (τ X1) X0
       grind)
    | exact superpose eq887 eq18
    | (have j1 := eq887 (τ X1) X0
       grind)
    | exact resolve eq18 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq944 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq887 X1 (σ X0)
       grind)
    | exact superpose eq887 eq36
    | (have j1 := eq887 X1 (σ X0)
       grind)
    | exact resolve eq36 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq887
  have eq957 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq944 X0 X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq944
    | (have j0 := eq944 X0 X1
       grind)
    | exact resolve eq944 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq2279 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq936 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq936
    | exact resolve eq936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq2338 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2279 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2279
    | (have j0 := eq2279 X0 X1
       grind)
    | exact resolve eq2279 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2279
  have eq13820 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq918 x y
       grind)
    | exact superpose eq918 eq16
    | (have j1 := eq918 x y
       grind)
    | exact resolve eq16 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq14010 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq13820
       have i₂ := eq2338 y x
       grind)
    | exact superpose eq2338 eq13820
    | (have j1 := eq2338 y x
       grind)
    | (have r₁ := eq13820
       have r₂ := eq2338 y x
       grind)
    | exact resolve eq13820 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13820
  have eq14011 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq14010
  have eq14016 : y ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14011
       grind)
    | exact superpose eq14011 eq12
    | exact resolve eq12 eq14011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14017 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq14011
       grind)
    | exact superpose eq14011 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14011
       grind)
    | exact resolve eq13 eq14011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14011
  have eq14058 : (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq14017
  have eq14059 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq14016
       have r₂ := eq14058
       grind)
    | exact resolve eq14016 eq14058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14016 eq14058
  have eq14252 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq320 x y
       have i₂ := eq14059
       grind)
    | exact superpose eq14059 eq320
    | (have j0 := eq320 x y
       grind)
    | exact resolve eq320 eq14059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq14262 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14252
  have eq14263 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq14262
  have eq14289 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq957 x (σ y)
       have i₂ := eq14263
       grind)
    | exact superpose eq14263 eq957
    | (have j0 := eq957 x (σ y)
       grind)
    | exact resolve eq957 eq14263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq14341 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq14263
  have eq14356 : (τ (σ y)) = (k x (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq14289
       have r₂ := eq14341
       grind)
    | exact resolve eq14289 eq14341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14289
  have eq14364 : y = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14356
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14356
    | exact resolve eq14356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14356
  have eq14536 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14059
       have i₂ := eq14364
       grind)
    | exact superpose eq14364 eq14059
    | exact resolve eq14059 eq14364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14059 eq14364
  have eq14568 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq14536
  have eq14575 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14568
       grind)
    | exact superpose eq14568 eq16
    | exact resolve eq16 eq14568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14593 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq14568
       grind)
    | exact superpose eq14568 eq12
    | exact resolve eq12 eq14568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14594 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq14568
       grind)
    | exact superpose eq14568 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq14568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14568
  have eq14648 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14594
       have r₂ := eq59 x
       grind)
    | exact resolve eq14594 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14594
  have eq14649 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14593
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq14593
    | exact resolve eq14593 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14593
  have eq14657 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14648
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq14648
    | exact resolve eq14648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14648
  have eq14659 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14657
       have i₂ := eq59 x
       grind)
    | exact superpose eq59 eq14657
    | exact resolve eq14657 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq14657
  have eq14660 : (σ (k x y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14659
       have r₂ := eq14649
       grind)
    | exact resolve eq14659 eq14649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14649 eq14659
  have eq14849 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2338 y x
       have i₂ := eq14660
       grind)
    | exact superpose eq14660 eq2338
    | (have j0 := eq2338 y x
       grind)
    | exact resolve eq2338 eq14660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14660
  have eq14931 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14849
       have r₂ := eq14575
       grind)
    | exact resolve eq14849 eq14575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14849
  have eq15100 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14575
       have i₂ := eq14931
       grind)
    | exact superpose eq14931 eq14575
    | exact resolve eq14575 eq14931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14575 eq14931
  have eq15148 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq15100
  have eq15149 : y = (M.op x x) := by grind
  clear eq15148
  have eq63812 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14341
       have i₂ := eq15149
       grind)
    | exact superpose eq15149 eq14341
    | exact resolve eq14341 eq15149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14341
  have eq63815 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq63812
  have eq63828 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63815
       grind)
    | exact superpose eq63815 eq16
    | exact resolve eq16 eq63815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63875 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq63815
       grind)
    | exact superpose eq63815 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq63815
       grind)
    | exact resolve eq12 eq63815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63815
  have eq63947 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq63875
  have eq63978 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq63947
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq63947
    | exact resolve eq63947 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63947
  have eq64567 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2338 y x
       have i₂ := eq63978
       grind)
    | exact superpose eq63978 eq2338
    | (have j0 := eq2338 y x
       grind)
    | exact resolve eq2338 eq63978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq63978
  have eq64704 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq64567
       have r₂ := eq63828
       grind)
    | exact resolve eq64567 eq63828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64567
  have eq64717 : y = (M.op x y) := by
    first
    | (have i₁ := eq64704
       have i₂ := eq15149
       grind)
    | exact superpose eq15149 eq64704
    | exact resolve eq64704 eq15149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15149 eq64704
  have eq65489 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq63828
       have i₂ := eq64717
       grind)
    | exact superpose eq64717 eq63828
    | exact resolve eq63828 eq64717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63828 eq64717
  have eq65581 : False := by grind
  exact eq65581

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pxy_pyx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq82 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq100 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq100 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq121 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq114 (σ X0) (σ X1)
       grind)
    | exact superpose eq114 eq15
    | exact resolve eq15 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq114 X0 X1
       grind)
    | exact superpose eq114 eq121
    | exact resolve eq121 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq121
  have eq286 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq130 x y
       grind)
    | exact superpose eq130 eq16
    | (have r₁ := eq16
       have r₂ := eq130 x y
       grind)
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq298 : False := by grind
  exact eq298

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_x_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq37 X1
       grind)
    | exact superpose eq37 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq186 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq163 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq163
    | (have j0 := eq163 X0 X1
       grind)
    | exact resolve eq163 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq191 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq186 X1 X0
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq186 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq186 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq186
  have eq195 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191
    | exact resolve eq191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq191 (σ X0) X1
       grind)
    | exact superpose eq191 eq15
    | (have j1 := eq191 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq209 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq195 X1 (τ X0)
       grind)
    | exact superpose eq195 eq18
    | (have j1 := eq195 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq195
  have eq530 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq209 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq209
    | exact resolve eq209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq572 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq530
    | (have j0 := eq530 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq1247 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq16
    | (have j1 := eq200 x y
       grind)
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq1341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1247
       have i₂ := eq572 x y
       grind)
    | exact superpose eq572 eq1247
    | (have j1 := eq572 (σ x) (σ y)
       grind)
    | (have r₁ := eq1247
       have r₂ := eq572 x y
       grind)
    | (have r₁ := eq1247
       have r₂ := eq572 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1247
       have r₂ := eq572 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1247 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1247
  have eq1342 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1341
  have eq1346 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1342
       grind)
    | exact superpose eq1342 eq10
    | exact resolve eq10 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1392 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1346
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1346
    | exact resolve eq1346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1393 : x = y := by grind
  clear eq1392
  have eq1401 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1393
       grind)
    | exact superpose eq1393 eq16
    | exact resolve eq16 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1402 : False := by grind
  exact eq1402

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq49 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq49 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq50 (σ X0)
       grind)
    | exact superpose eq50 eq15
    | exact resolve eq15 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq50 (τ X0)
       grind)
    | exact superpose eq50 eq18
    | exact resolve eq18 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq57
    | exact resolve eq57 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq57
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq98 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq272 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq237
    | (have j0 := eq237 X0 X1
       grind)
    | exact resolve eq237 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq237
  have eq276 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq272 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq272 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq272 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq279 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq276
    | (have j0 := eq276 X0 X1
       grind)
    | exact resolve eq276 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq276
  have eq757 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq279
    | exact resolve eq279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq279 (σ X0) X1
       grind)
    | exact superpose eq279 eq15
    | (have j1 := eq279 (σ X0) X1
       grind)
    | exact resolve eq15 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq784 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq769 X0 X1
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq769
    | (have j0 := eq769 X0 X1
       grind)
    | exact resolve eq769 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq769
  have eq801 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq757 (τ X1) X0
       grind)
    | exact superpose eq757 eq18
    | (have j1 := eq757 (τ X1) X0
       grind)
    | exact resolve eq18 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq757
  have eq2235 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq801 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq801
    | exact resolve eq801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq2294 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2235 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2235
    | (have j0 := eq2235 X0 X1
       grind)
    | exact resolve eq2235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235
  have eq13703 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq784 x y
       grind)
    | exact superpose eq784 eq16
    | (have j1 := eq784 x y
       grind)
    | exact resolve eq16 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13824 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq784 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq14073 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq13703
       have i₂ := eq2294 y x
       grind)
    | exact superpose eq2294 eq13703
    | (have j1 := eq2294 y x
       grind)
    | (have r₁ := eq13703
       have r₂ := eq2294 y x
       grind)
    | exact resolve eq13703 eq2294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14074 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq14073
  have eq14080 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq14074
       grind)
    | exact superpose eq14074 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14074
       grind)
    | exact resolve eq13 eq14074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14074
  have eq14121 : (k x y) = (M.op x x) ∨ x = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq14080
  have eq180518 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13824 x y
       have i₂ := eq14121
       grind)
    | exact superpose eq14121 eq13824
    | (have j0 := eq13824 x y
       grind)
    | exact resolve eq13824 eq14121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13824 eq14121
  have eq180529 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y x) := by grind
  clear eq180518
  have eq180530 : x = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq180529
  have eq180561 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq180530
       grind)
    | exact superpose eq180530 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq180530
       grind)
    | exact resolve eq12 eq180530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180530
  have eq180692 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq180561
  have eq181606 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13703
       have i₂ := eq180692
       grind)
    | exact superpose eq180692 eq13703
    | exact resolve eq13703 eq180692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13703 eq180692
  have eq181653 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq181606
  have eq181654 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq181653
  have eq182264 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181654
       grind)
    | exact superpose eq181654 eq16
    | exact resolve eq16 eq181654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182272 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq98 x (σ y)
       have i₂ := eq181654
       grind)
    | exact superpose eq181654 eq98
    | (have j0 := eq98 x (σ y)
       grind)
    | (have r₁ := eq98 x (σ y)
       have r₂ := eq181654
       grind)
    | exact resolve eq98 eq181654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq182470 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq182272
  have eq182547 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq182470
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq182470
    | exact resolve eq182470 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182470
  have eq187767 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq182547
       grind)
    | exact superpose eq182547 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq182547
       grind)
    | exact resolve eq12 eq182547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182547
  have eq187903 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq187767
  have eq187975 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq187903
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq187903
    | exact resolve eq187903 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187903
  have eq188073 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq187975
       have i₂ := eq181654
       grind)
    | exact superpose eq181654 eq187975
    | exact resolve eq187975 eq181654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181654 eq187975
  have eq188074 : (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq188073
  have eq188764 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2294 y x
       have i₂ := eq188074
       grind)
    | exact superpose eq188074 eq2294
    | (have j0 := eq2294 y x
       grind)
    | exact resolve eq2294 eq188074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294 eq188074
  have eq189043 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq188764
       have r₂ := eq182264
       grind)
    | exact resolve eq188764 eq182264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188764
  have eq190450 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq182264
       have i₂ := eq189043
       grind)
    | exact superpose eq189043 eq182264
    | exact resolve eq182264 eq189043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182264 eq189043
  have eq190594 : False := by grind
  exact eq190594

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq266 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq275 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq281 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq275 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq275 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq282 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq266
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq283 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq282
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq282
    | exact resolve eq282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq406 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq281 X0 (τ X1)
       grind)
    | exact superpose eq281 eq17
    | (have j1 := eq281 X0 (τ X1)
       grind)
    | exact resolve eq17 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq412 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq281 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1297 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq406 (τ X0) X1
       grind)
    | exact superpose eq406 eq18
    | (have j1 := eq406 (τ X0) X1
       grind)
    | exact resolve eq18 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq406
  have eq1302 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1297 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1297
    | (have j0 := eq1297 X0 X1
       grind)
    | exact resolve eq1297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1315 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1302 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1302
    | (have j0 := eq1302 X0 X1
       grind)
    | exact resolve eq1302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1318 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1315 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1315
    | (have j0 := eq1315 X0 X1
       grind)
    | exact resolve eq1315 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1385 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1318 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1318
    | (have j0 := eq1318 X1 (σ X0)
       grind)
    | exact resolve eq1318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1854 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1385 X0 X0
       have i₂ := eq281 X0 (σ X0)
       grind)
    | exact superpose eq281 eq1385
    | (have j0 := eq1385 X1 X0
       have j1 := eq281 X0 (σ X1)
       grind)
    | exact resolve eq1385 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq1385
  have eq1884 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1854 X0 X1
       have j1 := eq412 (σ X1) X0
       grind)
    | (have r₁ := eq1854 X1 X1
       have r₂ := eq412 (σ X1) X1
       grind)
    | exact resolve eq1854 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq1854
  have eq1975 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1884 (σ X0) X1
       grind)
    | exact superpose eq1884 eq22
    | (have j1 := eq1884 (σ X0) X1
       grind)
    | exact resolve eq22 eq1884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1884
  have eq1982 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1975 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1975
    | (have j0 := eq1975 X0 X1
       grind)
    | exact resolve eq1975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq1998 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1982 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1982
    | (have j0 := eq1982 X0 X1
       grind)
    | exact resolve eq1982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982
  have eq2007 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1998 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1998
    | (have j0 := eq1998 X0 X1
       grind)
    | exact resolve eq1998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998
  have eq2104 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2007 x y
       grind)
    | exact superpose eq2007 eq16
    | (have j1 := eq2007 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2007 x y
       grind)
    | exact resolve eq16 eq2007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2141 : x = (k y x) := by grind
  clear eq2104
  have eq2478 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq283
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq283
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq283 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2479 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq2478
  have eq2480 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq2479
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2479 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2481 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2480
       have i₂ := eq2141
       grind)
    | exact superpose eq2141 eq2480
    | exact resolve eq2480 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq2482 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2481
       have i₂ := eq2141
       grind)
    | exact superpose eq2141 eq2481
    | exact resolve eq2481 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481
  have eq2483 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq283
       have i₂ := eq2482
       grind)
    | exact superpose eq2482 eq283
    | exact resolve eq283 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq2482
  have eq2499 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2483
  have eq2500 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2499
       have i₂ := eq2141
       grind)
    | exact superpose eq2141 eq2499
    | exact resolve eq2499 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499
  have eq2501 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2500
  have eq2503 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2501
       grind)
    | exact superpose eq2501 eq16
    | exact resolve eq16 eq2501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501
  have eq2538 : (σ x) ≠ (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2503
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq2503
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq2503 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2539 : x = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq2538
  have eq2541 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq2539
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2539 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2539
  have eq2542 : x = (M.op x y) := by
    first
    | (have i₁ := eq2541
       have i₂ := eq2141
       grind)
    | exact superpose eq2141 eq2541
    | exact resolve eq2541 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141 eq2541
  have eq2543 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2503
       have i₂ := eq2542
       grind)
    | exact superpose eq2542 eq2503
    | exact resolve eq2503 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503 eq2542
  have eq2561 : False := by grind
  exact eq2561

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op y (M.op (M.op x y) (M.op X0 y))) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75
    | exact resolve eq75 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq82
    | exact resolve eq82 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq92 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq94 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq102 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ x)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq7250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq7251 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq7250
    | exact resolve eq7250 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7250
  have eq7262 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq7251
       have r₂ := eq27
       grind)
    | exact resolve eq7251 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7251
  have eq7264 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq7262
    | exact resolve eq7262 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7262
  have eq7267 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq7264 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq7264
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq7264
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq7264
       grind)
    | exact resolve eq13 eq7264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7264
  have eq7280 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq7267
  have eq7861 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq7280 eq55
    | exact resolve eq55 eq7280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq7280
  have eq7884 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq7861
    | exact resolve eq7861 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq7861
  have eq7887 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq7884
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq7884
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq7884
       have r₂ := eq13 x y
       grind)
    | exact resolve eq7884 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7884
  have eq7896 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq692 x y
       have i₂ := eq7887
       grind)
    | exact superpose eq7887 eq692
    | (have j0 := eq692 x y
       grind)
    | exact resolve eq692 eq7887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7898 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq7887
       grind)
    | exact superpose eq7887 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq7887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7887
  have eq7899 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7898
  have eq7901 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7896
  have eq7903 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7899
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7899
    | exact resolve eq7899 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7899
  have eq7904 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7903
  have eq7906 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7901
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7901
    | exact resolve eq7901 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7901
  have eq7917 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7906
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7906
    | exact resolve eq7906 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7906
  have eq7919 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7917
    | exact resolve eq7917 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7917
  have eq7920 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7919
  have eq7922 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7920
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7920
    | exact resolve eq7920 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7920
  have eq7924 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7922
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7922
    | exact resolve eq7922 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7922
  have eq7925 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7904
       grind)
    | exact superpose eq7904 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq7904
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7904
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7904
       grind)
    | exact resolve eq12 eq7904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7904
  have eq7940 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7925
  have eq7941 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7940
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7940
    | exact resolve eq7940 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7940
  have eq7942 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7941
  have eq7943 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7942
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7942
    | exact resolve eq7942 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7942
  have eq7988 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7924 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7924
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7924
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7924
       grind)
    | exact resolve eq12 eq7924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7924
  have eq8003 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7988
  have eq8004 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8003
    | exact resolve eq8003 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8003
  have eq8005 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8004
  have eq8006 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8005
    | exact resolve eq8005 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8005
  have eq8018 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq7943
       grind)
    | exact superpose eq7943 eq92
    | exact resolve eq92 eq7943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq8036 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8018
    | exact resolve eq8018 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8018
  have eq8074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8036 eq8006
    | exact resolve eq8006 eq8036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8006 eq8036
  have eq8078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8074
  have eq8080 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8078
       have r₂ := eq27
       grind)
    | exact resolve eq8078 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8078
  have eq8090 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8080 eq51
    | (have r₁ := eq51
       have r₂ := eq8080
       grind)
    | exact resolve eq51 eq8080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq8080
  have eq8104 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8090
  have eq8120 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8104 eq102
    | exact resolve eq102 eq8104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq8104
  have eq8147 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8120
    | exact resolve eq8120 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8120
  have eq8149 : y = (k y x) := by
    first
    | (have r₁ := eq8147
       have r₂ := eq50
       grind)
    | exact resolve eq8147 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq8147
  have eq8162 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq8149
       grind)
    | exact superpose eq8149 eq92
    | exact resolve eq92 eq8149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8170 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq692 y x
       have i₂ := eq8149
       grind)
    | exact superpose eq8149 eq692
    | (have j0 := eq692 y x
       grind)
    | exact resolve eq692 eq8149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq8172 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq8149
       grind)
    | exact superpose eq8149 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq8149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8173 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq8172
  have eq8175 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8170
  have eq8177 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8173
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8173
    | exact resolve eq8173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173
  have eq8179 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8175
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8175
    | exact resolve eq8175 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8175
  have eq8186 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8162
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8162
    | exact resolve eq8162 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8162
  have eq8189 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8179
    | exact resolve eq8179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8179
  have eq8191 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8189
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8189
    | exact resolve eq8189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8189
  have eq8193 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8191
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8191
    | exact resolve eq8191 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8191
  have eq8195 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8193
    | exact resolve eq8193 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8193
  have eq8224 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq8177
       grind)
    | exact superpose eq8177 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8177
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8177
       grind)
    | exact resolve eq12 eq8177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8226 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq8177
       grind)
    | exact superpose eq8177 eq14
    | exact resolve eq14 eq8177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8239 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq8224
  have eq8240 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8239
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8239
    | exact resolve eq8239 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8239
  have eq8241 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq8240
  have eq8242 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8241
       have i₂ := eq8149
       grind)
    | exact superpose eq8149 eq8241
    | exact resolve eq8241 eq8149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8149 eq8241
  have eq8243 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8242
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8242
    | exact resolve eq8242 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8242
  have eq8257 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8243 eq56
    | exact resolve eq56 eq8243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq8303 : y = (M.op y (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8243 eq215
    | exact resolve eq215 eq8243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq8243
  have eq8574 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8195 eq14
    | exact resolve eq14 eq8195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17485 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8226 y
       have i₂ := eq8177
       grind)
    | exact superpose eq8177 eq8226
    | exact resolve eq8226 eq8177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8177 eq8226
  have eq17514 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq17485
  have eq18042 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8195 eq8574
    | exact resolve eq8574 eq8195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8574
  have eq18078 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18042
  have eq18147 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8257 y
       have i₂ := eq8303
       grind)
    | exact superpose eq8303 eq8257
    | exact resolve eq8257 eq8303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8257 eq8303
  have eq18176 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq18147
  have eq18177 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17514
       have i₂ := eq18176
       grind)
    | exact superpose eq18176 eq17514
    | exact resolve eq17514 eq18176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17514 eq18176
  have eq18231 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18177
  have eq18232 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18231
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18231
    | exact resolve eq18231 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18231
  have eq18233 : x = (M.op x y) := by grind
  clear eq18232
  have eq18235 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18233 eq20
    | exact resolve eq20 eq18233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq18242 : (σ (k y x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq18233 eq94
    | exact resolve eq94 eq18233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq18233
  have eq18362 : (k (σ y) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq18242
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq18242
    | exact resolve eq18242 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq18242
  have eq18366 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18235
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18235
    | exact resolve eq18235 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18235
  have eq18375 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq8186 eq18362
    | exact resolve eq18362 eq8186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8186 eq18362
  have eq18654 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18366 eq26
    | exact resolve eq26 eq18366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq18726 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18366 eq8195
    | exact resolve eq8195 eq18366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8195
  have eq18752 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18366 eq18078
    | exact resolve eq18078 eq18366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18078 eq18366
  have eq18754 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have r₁ := eq18752
       have r₂ := eq27
       grind)
    | exact resolve eq18752 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18752
  have eq18758 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq18726
       have r₂ := eq27
       grind)
    | exact resolve eq18726 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18726
  have eq20325 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18758 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq18758
       grind)
    | exact resolve eq12 eq18758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18758
  have eq20352 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq20325
  have eq20353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18654 eq20352
    | exact resolve eq20352 eq18654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20352
  have eq20354 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq20353
       have r₂ := eq27
       grind)
    | exact resolve eq20353 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20353
  have eq20355 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq18654 eq20354
    | exact resolve eq20354 eq18654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20354
  have eq20356 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18375 eq20355
    | exact resolve eq20355 eq18375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18375 eq20355
  have eq21791 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq20356 eq57
    | exact resolve eq57 eq20356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq21794 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq20356 eq228
    | exact resolve eq228 eq20356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq20356
  have eq26869 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21794 eq21791
    | exact resolve eq21791 eq21794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21791 eq21794
  have eq26918 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26869 eq18754
    | exact resolve eq18754 eq26869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18754 eq26869
  have eq27007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18654 eq26918
    | exact resolve eq26918 eq18654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18654 eq26918
  have eq27030 : False := by grind
  exact eq27030

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxy_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54
    | (have j0 := eq54 (σ X0) (σ X1)
       grind)
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 y x
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq65 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq65 X1 X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq85 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq83 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq83 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq336 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq79
    | (have j1 := eq54 (σ y) (σ x)
       grind)
    | exact resolve eq79 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq339 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq336
  have eq340 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 x))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq339
       grind)
    | exact superpose eq339 eq9
    | exact resolve eq9 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq85
    | (have j0 := eq85 (τ X0) X1
       grind)
    | exact resolve eq85 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq85
  have eq534 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq537 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq534
    | (have j0 := eq534 X0 X1
       grind)
    | exact resolve eq534 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq579 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq537 (τ X0) X1
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq537
    | (have j0 := eq537 (τ X0) X1
       grind)
    | exact resolve eq537 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq537
  have eq1418 : x = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq340 y
       have i₂ := eq339
       grind)
    | exact superpose eq339 eq340
    | exact resolve eq340 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq1438 : x = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1418
  have eq1508 : x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq340 x
       have i₂ := eq1438
       grind)
    | exact superpose eq1438 eq340
    | exact resolve eq340 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq1438
  have eq1530 : x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1508
  have eq1609 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq1530
       grind)
    | exact superpose eq1530 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq1530
       grind)
    | exact resolve eq12 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1632 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609
  have eq1733 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq1632 y
       grind)
    | exact superpose eq1632 eq79
    | exact resolve eq79 eq1632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1632
  have eq1734 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1733
  have eq1735 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1734
  have eq1828 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq1735
       grind)
    | exact superpose eq1735 eq9
    | exact resolve eq9 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1828 (σ y)
       have i₂ := eq1735
       grind)
    | exact superpose eq1735 eq1828
    | exact resolve eq1828 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq2097 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1828 (σ x)
       have i₂ := eq1958
       grind)
    | exact superpose eq1958 eq1828
    | exact resolve eq1828 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828 eq1958
  have eq2241 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq2097
       grind)
    | exact resolve eq12 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2274 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2241 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241
  have eq2387 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2274 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq2274
    | exact resolve eq2274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2395 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq579 (σ x) X0
       have i₂ := eq2274 (σ x)
       grind)
    | exact superpose eq2274 eq579
    | (have j0 := eq579 (σ x) X0
       grind)
    | exact resolve eq579 eq2274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq2274
  have eq2426 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq2395 X0
       have i₂ := eq2097
       grind)
    | exact superpose eq2097 eq2395
    | (have j0 := eq2395 X0
       grind)
    | exact resolve eq2395 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097 eq2395
  have eq2427 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) := by
    intro X0
    first
    | (have j0 := eq2426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq2429 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq2427 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2427
    | exact resolve eq2427 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427
  have eq3247 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2387 X0
       have i₂ := eq2429 X0
       grind)
    | exact superpose eq2429 eq2387
    | exact resolve eq2387 eq2429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387 eq2429
  have eq3695 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3247 y
       grind)
    | exact superpose eq3247 eq16
    | (have r₁ := eq16
       have r₂ := eq3247 y
       grind)
    | exact resolve eq16 eq3247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3247
  have eq3761 : False := by grind
  exact eq3761
