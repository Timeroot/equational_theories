import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq58
  have eq82 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq88
  have eq265 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq279 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq283 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq279 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq279 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq293 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       have j1 := eq82 X0 (σ X1)
       grind)
    | (have r₁ := eq283 X0 X1
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq283 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq283
  have eq300 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq293
    | (have j0 := eq293 X0 X1
       grind)
    | exact resolve eq293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq301 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq305 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq301 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq301
    | exact resolve eq301 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq301 x y
       grind)
    | exact superpose eq301 eq16
    | exact resolve eq16 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq372 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq305 X0 (τ X1)
       grind)
    | exact superpose eq305 eq17
    | exact resolve eq17 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq305
  have eq398 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq372
    | exact resolve eq372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq411 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq398 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq398
    | exact resolve eq398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq440 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq316
       have i₂ := eq411 x y
       grind)
    | exact superpose eq411 eq316
    | exact resolve eq316 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq411
  have eq441 : False := by grind
  exact eq441

/-- `Equation1484`: `x = (y ◇ x) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation1484 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1484 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1484.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq112 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 X0
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq112 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq112
    | exact resolve eq112 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq169 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq171 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq1159 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq168 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq168
    | exact resolve eq168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1214 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1159 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1159
    | (have j0 := eq1159 X0 X1
       grind)
    | exact resolve eq1159 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq3072 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 x y
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq4523 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq171 X1 X0
       grind)
    | exact superpose eq171 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq171 X1 X0
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq171 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq171 (M.op X1 (τ X1)) X1
       grind)
    | exact resolve eq13 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq4537 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4523 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4523
  have eq4538 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4537 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4537
  have eq4550 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4538 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq4538
    | (have j0 := eq4538 X0 X1
       grind)
    | exact resolve eq4538 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq4538
  have eq7295 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3072
       have i₂ := eq1214 x y
       grind)
    | exact superpose eq1214 eq3072
    | (have j1 := eq1214 (σ x) (σ y)
       grind)
    | (have r₁ := eq3072
       have r₂ := eq1214 x y
       grind)
    | (have r₁ := eq3072
       have r₂ := eq1214 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3072
       have r₂ := eq1214 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3072 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq7296 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7295
  have eq7298 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7296
       grind)
    | exact superpose eq7296 eq16
    | exact resolve eq16 eq7296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7296
  have eq7299 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7298
       have r₂ := eq22 x
       grind)
    | exact resolve eq7298 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7298
  have eq7303 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq112 y x x
       have i₂ := eq7299
       grind)
    | exact superpose eq7299 eq112
    | exact resolve eq112 eq7299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7309 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7303 x
       have i₂ := eq7299
       grind)
    | exact superpose eq7299 eq7303
    | exact resolve eq7303 eq7299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7299 eq7303
  have eq7317 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq7309
  have eq7326 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq112 (σ y) x (σ x)
       have i₂ := eq7317
       grind)
    | exact superpose eq7317 eq112
    | exact resolve eq112 eq7317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq7392 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7326 (σ x)
       have i₂ := eq7317
       grind)
    | exact superpose eq7317 eq7326
    | exact resolve eq7326 eq7317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7317 eq7326
  have eq7405 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq7392
  have eq7412 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7405
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq7405
    | exact resolve eq7405 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7405
  have eq7425 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq114 y x
       have i₂ := eq7412
       grind)
    | exact superpose eq7412 eq114
    | exact resolve eq114 eq7412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq7412
  have eq7959 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7425 (M.op x (σ y))
       have i₂ := eq7425 x
       grind)
    | exact superpose eq7425 eq7425
    | exact resolve eq7425 eq7425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7425
  have eq7988 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq7959
  have eq7994 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7988
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq7988
    | exact resolve eq7988 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7988
  have eq7995 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq7994
  have eq8000 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7995
       grind)
    | exact superpose eq7995 eq10
    | exact resolve eq10 eq7995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7995
  have eq8061 : x = y ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq8000
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8000
    | exact resolve eq8000 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8000
  have eq8063 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8061
       grind)
    | exact superpose eq8061 eq16
    | exact resolve eq16 eq8061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8061
  have eq8064 : (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq8063
       have r₂ := eq22 x
       grind)
    | exact resolve eq8063 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8063
  have eq8186 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq8064
       grind)
    | exact superpose eq8064 eq10
    | exact resolve eq10 eq8064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8187 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op y y) X0
       have i₂ := eq8064
       grind)
    | exact superpose eq8064 eq15
    | exact resolve eq15 eq8064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8246 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8187 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq8187
    | exact resolve eq8187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8187
  have eq8247 : y = (M.op y y) := by
    first
    | (have i₁ := eq8186
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8186
    | exact resolve eq8186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8186
  have eq37096 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4550 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4550
    | (have j0 := eq4550 (M.op (σ X0) (σ X0)) (k X0 X1)
       grind)
    | exact resolve eq4550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4550
  have eq37260 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37096 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq37096
    | (have j0 := eq37096 X0 X1
       grind)
    | exact resolve eq37096 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37096
  have eq37284 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37260 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq37260
    | (have j0 := eq37260 X0 X1
       grind)
    | exact resolve eq37260 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37260
  have eq37292 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37284 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq37284
    | (have j0 := eq37284 X0 X1
       grind)
    | exact resolve eq37284 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37284
  have eq37454 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 (M.op y y))) ∨ (M.op (M.op y y) (M.op y y)) = (k (M.op y y) X0) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq8246 X0
       have i₂ := eq37292 (M.op y y) X0
       grind)
    | exact superpose eq37292 eq8246
    | (have j1 := eq37292 (M.op y y) X0
       grind)
    | exact resolve eq8246 eq37292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8246 eq37292
  have eq37621 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op (M.op y y) (M.op y y)) = (k (M.op y y) X0) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq37454 X0
       have i₂ := eq8247
       grind)
    | exact superpose eq8247 eq37454
    | (have j0 := eq37454 X0
       grind)
    | exact resolve eq37454 eq8247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37454
  have eq37694 : ∀ X0 : G, (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq37621 X0
       have i₂ := eq8247
       grind)
    | exact superpose eq8247 eq37621
    | (have j0 := eq37621 X0
       grind)
    | exact resolve eq37621 eq8247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37621
  have eq37736 : ∀ X0 : G, y = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq37694 X0
       have i₂ := eq8247
       grind)
    | exact superpose eq8247 eq37694
    | (have j0 := eq37694 X0
       grind)
    | exact resolve eq37694 eq8247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37694
  have eq37753 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq37736 X0
       have i₂ := eq8247
       grind)
    | exact superpose eq8247 eq37736
    | (have j0 := eq37736 X0
       grind)
    | exact resolve eq37736 eq8247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8247 eq37736
  have eq39667 : ∀ X0 : G, (k y X0) = (τ (σ (M.op X0 y))) ∨ y = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k y X0)
       have i₂ := eq37753 X0
       grind)
    | exact superpose eq37753 eq10
    | (have j1 := eq37753 X0
       grind)
    | exact resolve eq10 eq37753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37753
  have eq39753 : ∀ X0 : G, y = (k y X0) ∨ (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq39667 X0
       have i₂ := eq10 (M.op X0 y)
       grind)
    | exact superpose eq10 eq39667
    | (have j0 := eq39667 X0
       grind)
    | exact resolve eq39667 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39667
  have eq39890 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq39753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39753
  have eq39962 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq39890 X0
       have j1 := eq14 y X0
       grind)
    | (have r₁ := eq39890 x
       have r₂ := eq14 y x
       grind)
    | (have r₁ := eq39890 X0
       have r₂ := eq14 y (M.op X0 y)
       grind)
    | (have r₁ := eq39890 X0
       have r₂ := eq14 (M.op X0 y) y
       grind)
    | exact resolve eq39890 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39890
  have eq40161 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3072
       have i₂ := eq39962 x
       grind)
    | exact superpose eq39962 eq3072
    | (have j1 := eq39962 x
       grind)
    | exact resolve eq3072 eq39962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3072
  have eq40186 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 y
       have i₂ := eq39962 (τ X0)
       grind)
    | exact superpose eq39962 eq19
    | (have j1 := eq39962 (τ X0)
       grind)
    | exact resolve eq19 eq39962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq39962
  have eq40225 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq40161
  have eq40872 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq40186 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40186
    | exact resolve eq40186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40186
  have eq40990 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq40872 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq40872
    | (have j0 := eq40872 X0
       grind)
    | exact resolve eq40872 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40872
  have eq41190 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq40225
       grind)
    | exact superpose eq40225 eq16
    | exact resolve eq16 eq40225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41206 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq40225
       grind)
    | exact superpose eq40225 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq40225
       grind)
    | exact resolve eq13 eq40225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40225
  have eq41215 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq41206
  have eq41216 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq41215
  have eq41226 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq41216
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq41216
    | exact resolve eq41216 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41216
  have eq41242 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq41226
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq41226
    | exact resolve eq41226 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41226
  have eq41252 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq41242
       have i₂ := eq8064
       grind)
    | exact superpose eq8064 eq41242
    | exact resolve eq41242 eq8064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8064 eq41242
  have eq41320 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40990 x
       have i₂ := eq41252
       grind)
    | exact superpose eq41252 eq40990
    | (have j0 := eq40990 x
       grind)
    | exact resolve eq40990 eq41252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40990 eq41252
  have eq41402 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq41320
  have eq41434 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq41402
       have r₂ := eq41190
       grind)
    | exact resolve eq41402 eq41190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41190 eq41402
  have eq41476 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq41434
       grind)
    | exact superpose eq41434 eq10
    | exact resolve eq10 eq41434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41434
  have eq41563 : x = y ∨ x = y := by
    first
    | (have i₁ := eq41476
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41476
    | exact resolve eq41476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41476
  have eq41564 : x = y := by grind
  clear eq41563
  have eq41573 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41564
       grind)
    | exact superpose eq41564 eq16
    | exact resolve eq16 eq41564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41564
  have eq41788 : False := by grind
  exact eq41788

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pxy_pxx_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq24 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X1 (k X1 X1)
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 (k X0 X0)
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq41 X0 (k X0 X0)
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq42 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq42 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq49
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq43 X0 X1
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq43 X0 X1
       grind)
    | (have r₁ := eq54 X0 (M.op X0 X0)
       have r₂ := eq43 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq43 X0 (k X0 X1)
       grind)
    | exact resolve eq54 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq54
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq154 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq158 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq154 X0 X1
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq154 X0 X1
       have r₂ := eq60 X0 X1
       grind)
    | (have r₁ := eq154 X1 X1
       have r₂ := eq60 X1 X1
       grind)
    | exact resolve eq154 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq154
  have eq323 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq158 (σ X0) (σ X1)
       grind)
    | exact superpose eq158 eq15
    | exact resolve eq15 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 X1
       have i₂ := eq158 X0 X1
       grind)
    | exact superpose eq158 eq323
    | exact resolve eq323 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq323
  have eq332 : False := by grind
  exact eq332

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq25 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq19
    | (have j1 := eq25 (τ X0)
       grind)
    | exact resolve eq19 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75
    | (have j0 := eq75 X0
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq83 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq79
    | (have j0 := eq79 X0
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq83 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq83 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq83 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq112 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq27
    | (have j0 := eq27 X0 X1
       have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq87 (σ X0)
       grind)
    | exact superpose eq87 eq15
    | exact resolve eq15 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq133
    | exact resolve eq133 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq133
  have eq580 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq594 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq580
    | (have j0 := eq580 X0 X1
       grind)
    | exact resolve eq580 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq1699 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq112 x y
       grind)
    | exact superpose eq112 eq16
    | (have j1 := eq112 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq112 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq112 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq112 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1737 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1699
  have eq2341 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1737
       grind)
    | exact superpose eq1737 eq16
    | exact resolve eq16 eq1737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2344 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq1737
       grind)
    | exact superpose eq1737 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1737
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1737
       grind)
    | exact resolve eq12 eq1737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq2383 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq2344
  have eq2385 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2383
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2383
    | exact resolve eq2383 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq6216 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq594 x y
       have i₂ := eq2385
       grind)
    | exact superpose eq2385 eq594
    | (have j0 := eq594 x y
       grind)
    | exact resolve eq594 eq2385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq2385
  have eq6243 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6216
  have eq6259 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6243
       have r₂ := eq2341
       grind)
    | exact resolve eq6243 eq2341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341 eq6243
  have eq9290 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6259
       grind)
    | exact superpose eq6259 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq6259
       grind)
    | exact resolve eq12 eq6259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9363 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq9290
  have eq13634 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27 x y
       have i₂ := eq9363
       grind)
    | exact superpose eq9363 eq27
    | (have j0 := eq27 x y
       grind)
    | exact resolve eq27 eq9363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9363
  have eq13637 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13634
  have eq17372 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq13637
       grind)
    | exact superpose eq13637 eq16
    | exact resolve eq16 eq13637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13637
  have eq22385 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17372
       have i₂ := eq6259
       grind)
    | exact superpose eq6259 eq17372
    | exact resolve eq17372 eq6259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6259 eq17372
  have eq22386 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22385
  have eq22387 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq22386
  have eq26794 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22387
       grind)
    | exact superpose eq22387 eq10
    | exact resolve eq10 eq22387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22387
  have eq26868 : x = y ∨ x = y := by
    first
    | (have i₁ := eq26794
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26794
    | exact resolve eq26794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26794
  have eq26869 : x = y := by grind
  clear eq26868
  have eq33606 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26869
       grind)
    | exact superpose eq26869 eq16
    | exact resolve eq16 eq26869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26869
  have eq33607 : False := by grind
  exact eq33607

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq66 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22 eq36
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq78
    | (have j1 := eq86 y x
       grind)
    | exact resolve eq78 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq117
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq118 eq86
    | (have j0 := eq86 (σ y) (σ x)
       grind)
    | exact resolve eq86 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq145 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq67
    | exact resolve eq67 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq146 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq71
    | (have r₁ := eq71
       have r₂ := eq131
       grind)
    | exact resolve eq71 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq131
  have eq491 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq490
  have eq492 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq491
       have r₂ := eq145
       grind)
    | exact resolve eq491 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq491
  have eq495 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq492 eq118
    | exact resolve eq118 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq492
  have eq499 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq495
  have eq504 : y = (M.op x y) := by
    first
    | (have r₁ := eq499
       have r₂ := eq146
       grind)
    | exact resolve eq499 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq499
  have eq507 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq504 eq20
    | exact resolve eq20 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq511 : x ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq504 eq66
    | exact resolve eq66 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq512 : y ≠ y ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq504 eq70
    | (have r₁ := eq70
       have r₂ := eq504
       grind)
    | exact resolve eq70 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq504
  have eq517 : x = y ∨ y = (k y x) := by grind
  clear eq512
  have eq523 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq507
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq507
    | exact resolve eq507 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq608 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq523 eq26
    | exact resolve eq26 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq853 : y = (k y x) := by
    first
    | (have r₁ := eq517
       have r₂ := eq511
       grind)
    | exact resolve eq517 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq517
  have eq857 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq853
       grind)
    | exact superpose eq853 eq78
    | exact resolve eq78 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq853
  have eq864 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq523 eq857
    | exact resolve eq857 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq866 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq864
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq864
    | exact resolve eq864 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq864
  have eq867 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq523 eq866
    | exact resolve eq866 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq866
  have eq870 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq867 eq86
    | (have j0 := eq86 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq86 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq867
  have eq871 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq870
  have eq873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq608 eq871
    | exact resolve eq871 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq871
  have eq876 : False := by grind
  exact eq876

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq79 : x ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq111 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq87
    | (have j0 := eq87 (σ x) (σ X0)
       grind)
    | exact resolve eq87 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq87 x y
       grind)
    | exact superpose eq87 eq44
    | (have j1 := eq87 x y
       grind)
    | exact resolve eq44 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq129 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq126
    | exact resolve eq126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq130 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq129
    | exact resolve eq129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq149 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq170 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq149 eq16
    | exact resolve eq16 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq87
    | (have j0 := eq87 (σ x) (σ y)
       grind)
    | exact resolve eq87 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq197
    | exact resolve eq197 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq201 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq198
       have r₂ := eq27
       grind)
    | exact resolve eq198 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq203 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq201
    | exact resolve eq201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq205 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203 eq27
    | exact resolve eq27 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203 eq80
    | (have r₁ := eq80
       have r₂ := eq203
       grind)
    | exact resolve eq80 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq203
  have eq475 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq474
  have eq479 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq475 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq475
       grind)
    | exact resolve eq13 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq2418 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq479 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq2423 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2418
    | exact resolve eq2418 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq2425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq2423
    | exact resolve eq2423 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq2423
  have eq2433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2425
  have eq2436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2433
       have r₂ := eq205
       grind)
    | exact resolve eq2433 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq2433
  have eq2437 : x = (M.op x y) := by
    first
    | (have r₁ := eq2436
       have r₂ := eq27
       grind)
    | exact resolve eq2436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436
  have eq2438 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2437 eq20
    | exact resolve eq20 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2441 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq2437 eq79
    | (have r₁ := eq79
       have r₂ := eq2437
       grind)
    | exact resolve eq79 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2448 : (M.op y x) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq2441
  have eq2456 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2438
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2438
    | exact resolve eq2438 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2438
  have eq2528 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2456 eq26
    | exact resolve eq26 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2829 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k X0 y) = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2448
       grind)
    | exact superpose eq2448 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2448
       grind)
    | exact resolve eq13 eq2448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq3138 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2456 eq111
    | (have j0 := eq111 X0
       grind)
    | exact resolve eq111 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq3139 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2456 eq3138
    | (have j0 := eq3138 X0
       grind)
    | exact resolve eq3138 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3138
  have eq3256 : (σ (k x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq3139 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3139
    | (have j0 := eq3139 y
       grind)
    | exact resolve eq3139 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3139
  have eq3269 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2528 eq3256
    | exact resolve eq3256 eq2528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq3291 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq3269
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3269
    | exact resolve eq3269 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3269
  have eq3306 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2456 eq3291
    | exact resolve eq3291 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291
  have eq3313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2528 eq3306
    | exact resolve eq3306 eq2528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528 eq3306
  have eq3317 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq3313
       have r₂ := eq27
       grind)
    | exact resolve eq3313 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3313
  have eq3324 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq3317 eq170
    | exact resolve eq170 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq3317
  have eq3326 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2437 eq3324
    | exact resolve eq3324 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324
  have eq782462 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2829 X0
       have i₂ := eq3326
       grind)
    | exact superpose eq3326 eq2829
    | (have j0 := eq2829 X0
       grind)
    | exact resolve eq2829 eq3326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829
  have eq782477 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x y) := by
    first
    | (have j0 := eq782462 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782462
  have eq782481 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq782477
       have i₂ := eq3326
       grind)
    | exact superpose eq3326 eq782477
    | exact resolve eq782477 eq3326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326 eq782477
  have eq782484 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq782481
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq782481
    | exact resolve eq782481 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq782481
  have eq782485 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2437 eq782484
    | exact resolve eq782484 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2437 eq782484
  have eq782486 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq782485
  have eq782803 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq782486 eq15
    | exact resolve eq15 eq782486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782486
  have eq783452 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq782803
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq782803
    | exact resolve eq782803 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq782803
  have eq783544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2456 eq783452
    | exact resolve eq783452 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2456 eq783452
  have eq783558 : False := by grind
  exact eq783558

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq269 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq277 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq384 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq277 X1 X0
       grind)
    | exact superpose eq277 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq277 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq277 X0 X1
       grind)
    | exact resolve eq13 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq277 (σ x) (σ y)
       grind)
    | exact superpose eq277 eq16
    | (have j1 := eq277 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq384 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq395 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq390
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq390
    | exact resolve eq390 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq397 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq394 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq394 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq400 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq397 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq397
    | exact resolve eq397 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq397 X1 (τ X0)
       grind)
    | exact superpose eq397 eq17
    | (have j1 := eq397 X1 (τ X0)
       grind)
    | exact resolve eq17 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq428 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq397 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1611 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq422 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq422
    | exact resolve eq422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1635 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq422 X1 (τ X0)
       grind)
    | exact superpose eq422 eq18
    | (have j1 := eq422 X1 (τ X0)
       grind)
    | exact resolve eq18 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq422
  have eq1640 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1635 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1635
    | (have j0 := eq1635 X0 X1
       grind)
    | exact resolve eq1635 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq1655 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1611 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1611
    | (have j0 := eq1611 X0 X1
       grind)
    | exact resolve eq1611 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1656 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1640 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1640
    | (have j0 := eq1640 X0 X1
       grind)
    | exact resolve eq1640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640
  have eq1659 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1656 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1656
    | (have j0 := eq1656 X0 X1
       grind)
    | exact resolve eq1656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656
  have eq1718 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1659 X0 X1
       have i₂ := eq397 X0 X1
       grind)
    | exact superpose eq397 eq1659
    | (have j0 := eq1659 X1 X0
       have j1 := eq397 X1 X0
       grind)
    | exact resolve eq1659 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq1659
  have eq1778 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1718 X0 X1
       have j1 := eq428 X0 X1
       grind)
    | (have r₁ := eq1718 X0 X1
       have r₂ := eq428 X0 X1
       grind)
    | exact resolve eq1718 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq1718
  have eq1821 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1778 X1 (σ X0)
       grind)
    | exact superpose eq1778 eq22
    | (have j1 := eq1778 X1 (σ X0)
       grind)
    | exact resolve eq22 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1778
  have eq1854 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1821 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1821
    | (have j0 := eq1821 X0 X1
       grind)
    | exact resolve eq1821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq1874 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1854 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1854
    | (have j0 := eq1854 X0 X1
       grind)
    | exact resolve eq1854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1854
  have eq2628 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1874 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1874
    | exact resolve eq1874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq4046 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq395
       have i₂ := eq277 x y
       grind)
    | exact superpose eq277 eq395
    | (have j1 := eq277 x y
       grind)
    | exact resolve eq395 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4049 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq4046
  have eq4333 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq400 x y
       have i₂ := eq4049
       grind)
    | exact superpose eq4049 eq400
    | (have j0 := eq400 x y
       grind)
    | exact resolve eq400 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq4049
  have eq4342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq4333
       have r₂ := eq395
       grind)
    | exact resolve eq4333 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq4333
  have eq4344 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq4342
       have r₂ := eq16
       grind)
    | exact resolve eq4342 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4342
  have eq4347 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4344
       grind)
    | exact superpose eq4344 eq16
    | exact resolve eq16 eq4344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4344
  have eq4395 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4347
       have i₂ := eq2628 x y
       grind)
    | exact superpose eq2628 eq4347
    | (have j1 := eq2628 x y
       grind)
    | exact resolve eq4347 eq2628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq4400 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq4347
       have i₂ := eq1655 x y
       grind)
    | exact superpose eq1655 eq4347
    | (have j1 := eq1655 x y
       grind)
    | (have r₁ := eq4347
       have r₂ := eq1655 x y
       grind)
    | exact resolve eq4347 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655 eq4347
  have eq4401 : y = (k x y) := by grind
  clear eq4400
  have eq4408 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq4395
       have r₂ := eq16
       grind)
    | exact resolve eq4395 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4395
  have eq4435 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4408
       have i₂ := eq277 x y
       grind)
    | exact superpose eq277 eq4408
    | (have j1 := eq277 x y
       grind)
    | exact resolve eq4408 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq4438 : (M.op x y) = (k x y) := by grind
  clear eq4435
  have eq4439 : y = (M.op x y) := by
    first
    | (have i₁ := eq4438
       have i₂ := eq4401
       grind)
    | exact superpose eq4401 eq4438
    | exact resolve eq4438 eq4401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4401 eq4438
  have eq4440 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4408
       have i₂ := eq4439
       grind)
    | exact superpose eq4439 eq4408
    | exact resolve eq4408 eq4439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4408 eq4439
  have eq4464 : False := by grind
  exact eq4464

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq280 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq267 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq267
    | (have j0 := eq267 X0
       grind)
    | exact resolve eq267 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq267
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq280
    | (have j0 := eq280 X0
       grind)
    | exact resolve eq280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq284 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq283 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq283 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq283 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq294 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq284 (σ X0)
       grind)
    | exact superpose eq284 eq15
    | exact resolve eq15 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq294 X0
       have i₂ := eq284 X0
       grind)
    | exact superpose eq284 eq294
    | exact resolve eq294 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq294
  have eq359 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1486 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq362 (τ X1) (τ X0)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq362
    | (have j0 := eq362 (τ X0) (τ X1)
       grind)
    | exact resolve eq362 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1493 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1486 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1486
    | (have j0 := eq1486 X0 X1
       grind)
    | exact resolve eq1486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486
  have eq1496 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1493 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1493
    | (have j0 := eq1493 X0 X1
       grind)
    | exact resolve eq1493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1498 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1496 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1496
    | (have j0 := eq1496 X0 X1
       grind)
    | exact resolve eq1496 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1499 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1498 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1498
    | (have j0 := eq1498 X0 X1
       grind)
    | exact resolve eq1498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1500 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1499 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1499
    | (have j0 := eq1499 X0 X1
       grind)
    | exact resolve eq1499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1501 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1500 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1500
    | (have j0 := eq1500 X0 X1
       grind)
    | exact resolve eq1500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq2124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq359
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq359
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq359
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq359
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq359 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq2125 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2124
  have eq14431 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2125
       grind)
    | exact superpose eq2125 eq16
    | exact resolve eq16 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq14432 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14431
       have r₂ := eq307 x
       grind)
    | exact resolve eq14431 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14431
  have eq14434 : y ≠ y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14432
       grind)
    | exact superpose eq14432 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq14432
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14432
       grind)
    | exact resolve eq12 eq14432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14432
  have eq14452 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14434
  have eq14458 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq362 x y
       have i₂ := eq14452
       grind)
    | exact superpose eq14452 eq362
    | (have j0 := eq362 x y
       grind)
    | exact resolve eq362 eq14452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq14452
  have eq14464 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14458
  have eq14465 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq14464
  have eq14668 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14465
       grind)
    | exact superpose eq14465 eq16
    | exact resolve eq16 eq14465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14670 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq14465
       grind)
    | exact superpose eq14465 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14465
       grind)
    | exact resolve eq12 eq14465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14465
  have eq14688 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq14670
  have eq14691 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14688
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq14688
    | exact resolve eq14688 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14688
  have eq14878 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14691
       grind)
    | exact superpose eq14691 eq10
    | exact resolve eq10 eq14691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14691
  have eq14949 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14878
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14878
    | exact resolve eq14878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14878
  have eq14960 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14949
       grind)
    | exact superpose eq14949 eq16
    | exact resolve eq16 eq14949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14949
  have eq14961 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq14960
       have r₂ := eq307 x
       grind)
    | exact resolve eq14960 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14960
  have eq15163 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq14961
       grind)
    | exact superpose eq14961 eq10
    | exact resolve eq10 eq14961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14961
  have eq15239 : y = (k y x) := by
    first
    | (have i₁ := eq15163
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq15163
    | exact resolve eq15163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15163
  have eq15259 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1501 y x
       have i₂ := eq15239
       grind)
    | exact superpose eq15239 eq1501
    | (have j0 := eq1501 x y
       grind)
    | (have r₁ := eq1501 y x
       have r₂ := eq15239
       grind)
    | exact resolve eq1501 eq15239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq15239
  have eq15262 : x = y ∨ y = (M.op x y) := by grind
  clear eq15259
  have eq15430 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15262
       grind)
    | exact superpose eq15262 eq16
    | exact resolve eq16 eq15262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15262
  have eq15435 : y = (M.op x y) := by
    first
    | (have r₁ := eq15430
       have r₂ := eq307 x
       grind)
    | exact resolve eq15430 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15430
  have eq15439 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14668
       have i₂ := eq15435
       grind)
    | exact superpose eq15435 eq14668
    | exact resolve eq14668 eq15435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14668 eq15435
  have eq15460 : (σ x) = (σ y) := by grind
  clear eq15439
  have eq15632 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15460
       grind)
    | exact superpose eq15460 eq10
    | exact resolve eq10 eq15460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15460
  have eq15711 : x = y := by
    first
    | (have i₁ := eq15632
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15632
    | exact resolve eq15632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15632
  have eq15726 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15711
       grind)
    | exact superpose eq15711 eq16
    | exact resolve eq16 eq15711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15711
  have eq15732 : False := by grind
  exact eq15732
