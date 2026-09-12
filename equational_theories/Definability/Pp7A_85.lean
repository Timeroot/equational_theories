import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq72 (σ X0)
       grind)
    | exact superpose eq72 eq10
    | exact resolve eq10 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq72 sF2
       grind)
    | exact superpose eq72 eq50
    | exact resolve eq50 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq72 x
       grind)
    | exact superpose eq72 eq76
    | exact resolve eq76 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq74
    | exact resolve eq74 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq72 sF3
       grind)
    | exact superpose eq72 eq104
    | exact resolve eq104 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq72 y
       grind)
    | exact superpose eq72 eq108
    | exact resolve eq108 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq72 sF1
       grind)
    | exact superpose eq72 eq119
    | exact resolve eq119 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq124 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq122
       have i₂ := eq72 sF0
       grind)
    | exact superpose eq72 eq122
    | exact resolve eq122 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq146 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : (M.op x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : (M.op x y) ≠ (M.op x (M.op x y)) ∨ (k x (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq236 eq13
    | exact resolve eq13 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq72 (τ X0)
       grind)
    | exact superpose eq72 eq35
    | exact resolve eq35 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq277 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq266 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq266
    | exact resolve eq266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq277
    | exact resolve eq277 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq277
  have eq396 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq14
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq415 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 y)
       have i₂ := eq237 X0 y
       grind)
    | (have i₁ := eq56 (M.op x y)
       have i₂ := eq237 X0 y
       grind)
    | exact superpose eq237 eq56
    | exact resolve eq56 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq415 X0
       have i₂ := eq237 X0 (M.op sF0 y)
       grind)
    | (have i₁ := eq415 x
       have i₂ := eq237 X0 (M.op sF0 y)
       grind)
    | exact superpose eq237 eq415
    | exact resolve eq415 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq427 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq418 X0
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq418
    | exact resolve eq418 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq451 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq247 eq56
    | exact resolve eq56 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq247 eq57
    | exact resolve eq57 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq247 eq452
    | exact resolve eq452 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq454 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq247 eq451
    | exact resolve eq451 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq462 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq57 eq453
    | exact resolve eq453 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq463 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq454 X0
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq454
    | exact resolve eq454 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq495 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X0 y) X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 y X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq51
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X2 X1 X0 X0
       have i₂ := eq55 X0 X1 X0
       grind)
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq823 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq247 eq728
    | (have j0 := eq728 X0 (σ x)
       grind)
    | exact resolve eq728 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq824 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq727 X0 x
       have i₂ := eq237 x X0
       grind)
    | (have i₁ := eq727 x x
       have i₂ := eq237 X0 x
       grind)
    | exact superpose eq237 eq727
    | (have j0 := eq727 X0 x
       grind)
    | exact resolve eq727 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq1187 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 X1)
       have i₂ := eq52 X1 y (M.op X0 X1) X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op x X0)
       have i₂ := eq52 X0 sF3 (M.op x X0) x
       grind)
    | exact superpose eq52 eq57
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1236 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq247 eq1188
    | exact resolve eq1188 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1237 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 X1
       have i₂ := eq237 (M.op X0 X1) (M.op X1 (M.op X1 y))
       grind)
    | exact superpose eq237 eq1187
    | exact resolve eq1187 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1262 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq1236
    | exact resolve eq1236 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1263 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1237 X0 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq1237
    | exact resolve eq1237 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1507 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq146 eq279
    | exact resolve eq279 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq279
  have eq1533 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq247 eq1507
    | exact resolve eq1507 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507
  have eq1535 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq462 eq1533
    | exact resolve eq1533 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1536 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op y y))) := by
    first
    | (have i₁ := eq1535
       have i₂ := eq237 y (M.op y y)
       grind)
    | exact superpose eq237 eq1535
    | exact resolve eq1535 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1537 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq427 eq1536
    | exact resolve eq1536 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq1538 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq124 eq1537
    | exact resolve eq1537 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq2251 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq247 eq823
    | exact resolve eq823 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq2340 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2251 eq51
    | exact resolve eq51 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq2364 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2340 X0
       have i₂ := eq14 sF4 sF3 sF4
       grind)
    | exact superpose eq14 eq2340
    | exact resolve eq2340 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340
  have eq2370 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | (have i₁ := eq2364 x
       have i₂ := eq14 sF4 sF3 x
       grind)
    | exact superpose eq14 eq2364
    | exact resolve eq2364 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2364
  have eq2371 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq462 eq2370
    | exact resolve eq2370 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq2372 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1538 eq2371
    | exact resolve eq2371 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq2383 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq824 y
       have i₂ := eq237 sF0 y
       grind)
    | exact superpose eq237 eq824
    | exact resolve eq824 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq2439 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2383 eq51
    | exact resolve eq51 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2463 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2439 X0
       have i₂ := eq14 sF0 y sF0
       grind)
    | exact superpose eq14 eq2439
    | exact resolve eq2439 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq2469 : (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2463 x
       have i₂ := eq14 sF0 y x
       grind)
    | exact superpose eq14 eq2463
    | exact resolve eq2463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463
  have eq2470 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq427 eq2469
    | exact resolve eq2469 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469
  have eq2582 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq57 eq1262
    | exact resolve eq1262 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1262
  have eq2680 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq462 eq2582
    | exact resolve eq2582 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq2582
  have eq2697 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1538 eq2680
    | exact resolve eq2680 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq2680
  have eq2705 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq2372 eq2697
    | exact resolve eq2697 eq2372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372 eq2697
  have eq2727 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2705 y
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq2705
    | exact resolve eq2705 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705
  have eq2794 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq1263 X0 (M.op X0 y)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq1263
    | exact resolve eq1263 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2916 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq427 eq2794
    | exact resolve eq2794 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794
  have eq2935 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2470 eq2916
    | exact resolve eq2916 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470 eq2916
  have eq3017 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1263 eq2935
    | exact resolve eq2935 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3018 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq463 eq2935
    | exact resolve eq2935 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq2935
  have eq4175 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) (M.op y y))) X0) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq396 (M.op y y) X0
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq396
    | exact resolve eq396 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq396
  have eq4352 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op y y) (M.op y y))) X0) := by
    intro X0
    first
    | exact superpose eq250 eq4175
    | exact resolve eq4175 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq4175
  have eq4386 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op x y) (M.op y y))) X0) := by
    intro X0
    first
    | (have i₁ := eq4352 X0
       have i₂ := eq237 y (M.op y y)
       grind)
    | exact superpose eq237 eq4352
    | exact resolve eq4352 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4352
  have eq4402 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq427 eq4386
    | exact resolve eq4386 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq4386
  have eq4414 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq124 eq4402
    | exact resolve eq4402 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq4402
  have eq4418 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq247 eq4414
    | exact resolve eq4414 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq4414
  have eq4420 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2727 eq4418
    | exact resolve eq4418 eq2727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727 eq4418
  have eq4422 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq3018 eq4420
    | exact resolve eq4420 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018 eq4420
  have eq4873 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op y X1)) y) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq495 (M.op X2 X1) X3 y
       have i₂ := eq51 X2 X1 y X0
       grind)
    | exact superpose eq51 eq495
    | exact resolve eq495 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4897 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq1263 eq495
    | exact resolve eq495 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5058 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (M.op x y) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq4422 eq4897
    | exact resolve eq4897 eq4422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4897
  have eq5074 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq4873 x X1 X2 X3
       have i₂ := eq237 (M.op x (M.op y X1)) X3
       grind)
    | exact superpose eq237 eq4873
    | exact resolve eq4873 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq4873
  have eq5128 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5058 X0 X1
       have i₂ := eq495 X0 X1 sF0
       grind)
    | exact superpose eq495 eq5058
    | exact resolve eq5058 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq5058
  have eq5142 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq3017 eq5074
    | (have j0 := eq5074 y x X3
       grind)
    | exact resolve eq5074 eq3017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017 eq5074
  have eq5189 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (σ x) (σ y)) X3) := by
    intro X3
    first
    | exact superpose eq4422 eq5142
    | exact resolve eq5142 eq4422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4422 eq5142
  have eq5450 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq5189 eq5128
    | exact resolve eq5128 eq5189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5128 eq5189
  have eq6428 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5450 X1 X2
       have i₂ := eq53 sF0 X1 X2 x
       grind)
    | (have i₁ := eq5450 X1 X2
       have i₂ := eq53 X0 X1 X2 sF0
       grind)
    | exact superpose eq53 eq5450
    | exact resolve eq5450 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq7574 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1263 eq653
    | exact resolve eq653 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq1263
  have eq7893 : ∀ X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op x y) X2) := by
    intro X1 X2
    first
    | exact superpose eq5450 eq7574
    | exact resolve eq7574 eq5450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5450 eq7574
  have eq9414 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq739 X0 X1 X2
       have i₂ := eq7893 X0 X0
       grind)
    | (have i₁ := eq739 (M.op x y) X1 X2
       have i₂ := eq7893 X1 (M.op (M.op x y) (M.op x y))
       grind)
    | exact superpose eq7893 eq739
    | exact resolve eq739 eq7893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq9467 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq9414 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9414
    | (have j0 := eq9414 X0 y x
       grind)
    | exact resolve eq9414 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9414
  have eq25435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq25435
    | exact resolve eq25435 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25435
  have eq25447 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq25436
       have r₂ := eq28
       grind)
    | exact resolve eq25436 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25436
  have eq25452 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq25447 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq25447
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25447
       grind)
    | exact resolve eq13 eq25447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25447
  have eq25473 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq25452
  have eq25496 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq25473 eq96
    | exact resolve eq96 eq25473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq25473
  have eq25506 : y = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq25496
  have eq25536 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6428 y x X0
       have i₂ := eq25506
       grind)
    | exact superpose eq25506 eq6428
    | exact resolve eq6428 eq25506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25890 : (M.op y x) = (M.op x (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq236 eq25536
    | exact resolve eq25536 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25536
  have eq26617 : y = (M.op x (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25506
       have i₂ := eq25890
       grind)
    | exact superpose eq25890 eq25506
    | exact resolve eq25506 eq25890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25506 eq25890
  have eq26639 : y = (M.op x (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq26617
  have eq26688 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26639 eq7893
    | exact resolve eq7893 eq26639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7893
  have eq26691 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq236 eq26688
    | exact resolve eq26688 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq26688
  have eq26707 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26691
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26691
    | exact resolve eq26691 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26691
  have eq26724 : y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26707 eq26639
    | exact resolve eq26639 eq26707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26639 eq26707
  have eq26744 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq26724
  have eq26758 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26744 eq30
    | exact resolve eq30 eq26744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26744
  have eq26882 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq26758
    | exact resolve eq26758 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26758
  have eq26883 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq26882
  have eq26909 : y = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26883 eq30
    | exact resolve eq30 eq26883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26883
  have eq27038 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq26909
    | exact resolve eq26909 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq26909
  have eq27039 : y = (M.op x y) ∨ x = y := by grind
  clear eq27038
  have eq27101 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq27039 eq21
    | exact resolve eq21 eq27039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27142 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | exact superpose eq27039 eq242
    | exact resolve eq242 eq27039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq27265 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq27142
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27142
    | exact resolve eq27142 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27142
  have eq27304 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27101
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27101
    | exact resolve eq27101 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27101
  have eq27310 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have r₁ := eq27265
       have r₂ := eq27039
       grind)
    | exact resolve eq27265 eq27039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27039 eq27265
  have eq27327 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq27310
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27310
    | exact resolve eq27310 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27310
  have eq27606 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq27327
       grind)
    | exact superpose eq27327 eq45
    | exact resolve eq45 eq27327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq27327
  have eq27633 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq27606
    | exact resolve eq27606 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27606
  have eq27772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27633 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq27633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27633
  have eq27782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq27772
    | exact resolve eq27772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27772
  have eq27793 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq27782
       have r₂ := eq28
       grind)
    | exact resolve eq27782 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27782
  have eq31343 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27793 eq6428
    | exact resolve eq6428 eq27793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6428
  have eq71045 : (σ y) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31343 eq27793
    | exact resolve eq27793 eq31343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27793 eq31343
  have eq71201 : (σ y) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq71045
  have eq71393 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq71201 eq9467
    | exact resolve eq9467 eq71201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9467 eq71201
  have eq71460 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq71393
    | exact resolve eq71393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71393
  have eq71474 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq71460 eq28
    | exact resolve eq28 eq71460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71460
  have eq71596 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq71474
       have r₂ := eq27304
       grind)
    | exact resolve eq71474 eq27304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27304 eq71474
  have eq71606 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq71596 eq30
    | exact resolve eq30 eq71596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq71596
  have eq71999 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq71606
    | exact resolve eq71606 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq71606
  have eq72000 : x = y := by grind
  clear eq71999
  have eq72020 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq72000
       grind)
    | exact superpose eq72000 eq19
    | exact resolve eq19 eq72000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq72021 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq72000
       grind)
    | exact superpose eq72000 eq25
    | exact resolve eq25 eq72000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq72000
  have eq72162 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq72021
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq72021
    | exact resolve eq72021 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq72021
  have eq72184 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq72162 eq27
    | exact resolve eq27 eq72162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq72162
  have eq72575 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq72184 eq77
    | exact resolve eq77 eq72184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq72184
  have eq72658 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq72575
       have i₂ := eq72020
       grind)
    | exact superpose eq72020 eq72575
    | exact resolve eq72575 eq72020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72020 eq72575
  have eq72676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72658 eq15
    | exact resolve eq15 eq72658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72658
  have eq72750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq72676
    | exact resolve eq72676 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq72676
  have eq72770 : False := by grind
  exact eq72770

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pyx_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X2 X1) X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X1) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X1 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X2 X0
       have i₂ := eq9 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X2 X1)) ∨ (k X2 (M.op X2 X1)) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X2 X1)
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X2 (M.op X2 X1)
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 (M.op X3 X1)) = (k (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X3 X1) X2
       have i₂ := eq53 X3 X1 X2 X0
       grind)
    | (have i₁ := eq13 (M.op X3 X1) X2
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 (M.op X3 X1) X2
       grind)
    | (have r₁ := eq13 (M.op (M.op X3 X2) X2) X2
       have r₂ := eq53 (M.op X3 X2) X2 X2 X3
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X2) X2) X2
       have r₂ := eq53 X0 X2 X2 (M.op X0 X2)
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 X1) ∨ (M.op X0 X0) = X0 ∨ (k (M.op X2 X1) X0) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X2 X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X2 X1) X0
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (k X2 (M.op X2 X1)) ∨ (M.op (M.op X0 X1) X2) ≠ X2 ∨ (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188 X0 X1 X2
       have i₂ := eq9 X2 X1 X2
       grind)
    | exact superpose eq9 eq188
    | (have j0 := eq188 X0 X1 X2
       grind)
    | exact resolve eq188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq197 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (M.op X2 (M.op X2 X1)) = (k X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq195 X0 X1 X2
       have j1 := eq12 X2 (M.op X2 X1)
       grind)
    | (have r₁ := eq195 X0 X1 X2
       have r₂ := eq12 X0 (M.op X2 X1)
       grind)
    | exact resolve eq195 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq282 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 (M.op X3 (M.op X1 X4)))) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq112 X2 (M.op X3 (M.op X1 X4)) X0
       have i₂ := eq110 X3 X1 X4 X0
       grind)
    | exact superpose eq110 eq112
    | exact resolve eq112 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X0)) = (M.op X2 (M.op X2 (M.op X3 (M.op X1 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq282 X0 X1 X2 X3 X4
       have i₂ := eq112 X2 X0 (M.op X0 X1)
       grind)
    | exact superpose eq112 eq282
    | exact resolve eq282 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq335 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X2 X0)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq324 X0 x X2 X3 x
       have i₂ := eq112 X2 X3 (M.op x x)
       grind)
    | exact superpose eq112 eq324
    | exact resolve eq324 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq359 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq335 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq335
    | exact resolve eq335 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq479 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq359 X0 X1 X2 x
       have i₂ := eq359 X3 X4 X2 x
       grind)
    | exact superpose eq359 eq359
    | exact resolve eq359 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq440 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq440
    | (have j0 := eq440 (σ X0) (σ X1)
       grind)
    | exact resolve eq440 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq440 X0 (τ X1)
       grind)
    | exact superpose eq440 eq18
    | (have j1 := eq440 X0 (τ X1)
       grind)
    | exact resolve eq18 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X2 X1 X0 X0
       have i₂ := eq55 X0 X1 X0
       grind)
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1198 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X4 X1) X0)) = (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X2 X1))) X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq51 X4 X1 X0 (M.op x X2)
       have i₂ := eq52 X2 X1 X0 x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq52
  have eq1276 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X4 X1) X0)) = (M.op X0 (M.op X0 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1198 X0 X1 X2 X4
       have i₂ := eq9 X0 (M.op X2 (M.op X2 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq1198
    | exact resolve eq1198 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1307 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (M.op (M.op X4 X1) X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1276 X0 X1 X2 X4
       have i₂ := eq112 X0 X2 (M.op X2 X1)
       grind)
    | exact superpose eq112 eq1276
    | exact resolve eq1276 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1338 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op (M.op X3 X4) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1307 X2 X4 X1 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq1307
    | exact resolve eq1307 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq1556 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq197 x X1 X0
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq197
    | (have j0 := eq197 X0 X1 X0
       grind)
    | exact resolve eq197 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq1596 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1556 X0 X1
       have j1 := eq440 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq1556 X0 X1
       have r₂ := eq440 X0 (M.op X0 X1)
       grind)
    | exact resolve eq1556 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1647 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = (τ (M.op (σ X0) (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) X1)
       have i₂ := eq1596 (σ X0) X1
       grind)
    | exact superpose eq1596 eq28
    | exact resolve eq28 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1656 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq541 x y
       grind)
    | exact superpose eq541 eq16
    | (have j1 := eq541 x y
       grind)
    | exact resolve eq16 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1659 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq541 X0 X1
       grind)
    | exact superpose eq541 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq541 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq541 X0 X1
       grind)
    | exact resolve eq13 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1684 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X0 X1))) = (k (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1596 (σ X0) (σ X1)
       have i₂ := eq541 X0 X1
       grind)
    | exact superpose eq541 eq1596
    | (have j1 := eq541 X0 X1
       grind)
    | exact resolve eq1596 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1686 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq541 X0 X0
       grind)
    | exact superpose eq541 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq541 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq541 X1 X1
       grind)
    | exact resolve eq12 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1687 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq541 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq1688 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1686 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq1686 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq1686 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq1689 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X0 X1))) = (σ (k X0 (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1684 X0 X1
       have i₂ := eq15 X0 (k X0 X1)
       grind)
    | exact superpose eq15 eq1684
    | (have j0 := eq1684 X0 X1
       grind)
    | exact resolve eq1684 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1690 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1659 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq1659 X0 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq1659 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq1659 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq1693 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1690 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1690
    | (have j0 := eq1690 X0 X1
       grind)
    | exact resolve eq1690 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq1958 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) ≠ (M.op (M.op X0 (M.op X0 X1)) X2) ∨ (M.op X2 X2) = X2 ∨ (k (M.op X3 X0) X2) = (M.op X2 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq192 X2 X0 X3
       have i₂ := eq55 X0 X1 X2
       grind)
    | exact superpose eq55 eq192
    | (have j0 := eq192 X2 X0 X3
       grind)
    | (have r₁ := eq192 X2 X2 (M.op X2 (M.op X2 X1))
       have r₂ := eq55 X2 X1 X2
       grind)
    | exact resolve eq192 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq192
  have eq3701 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1687 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1687
    | (have j0 := eq1687 (τ X0) (τ X1)
       grind)
    | exact resolve eq1687 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3721 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3701 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3701
    | (have j0 := eq3701 X0 X1
       grind)
    | exact resolve eq3701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3701
  have eq3725 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3721 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3721
    | (have j0 := eq3721 X0 X1
       grind)
    | exact resolve eq3721 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721
  have eq3726 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3725 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3725
    | (have j0 := eq3725 X0 X1
       grind)
    | exact resolve eq3725 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq3727 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3726 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3726
    | (have j0 := eq3726 X0 X1
       grind)
    | exact resolve eq3726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3726
  have eq3729 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3727 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq3727
    | (have j0 := eq3727 (τ X0) (τ X1)
       grind)
    | exact resolve eq3727 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3805 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq547
    | exact resolve eq547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq3838 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3805 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3805
    | (have j0 := eq3805 X0 X1
       grind)
    | exact resolve eq3805 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq3862 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (τ (k X2 (σ (M.op X0 X1)))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k X0 X1)
       have i₂ := eq3838 X1 X0
       grind)
    | exact superpose eq3838 eq22
    | (have j1 := eq3838 X1 X0
       grind)
    | exact resolve eq22 eq3838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3838
  have eq3871 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (k (τ X2) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3862 X0 X1 X2
       have i₂ := eq22 X2 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq3862
    | (have j0 := eq3862 X0 X1 X2
       grind)
    | exact resolve eq3862 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3862
  have eq3982 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1688 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1688
    | (have j0 := eq1688 (τ X0) X1
       grind)
    | exact resolve eq1688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1688
  have eq3992 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3982 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3982
    | (have j0 := eq3982 X0 X1
       grind)
    | exact resolve eq3982 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3982
  have eq3999 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3992 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3992
    | (have j0 := eq3992 X0 X1
       grind)
    | exact resolve eq3992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq9256 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1656
       have i₂ := eq440 x y
       grind)
    | exact superpose eq440 eq1656
    | (have j1 := eq440 (σ x) (σ y)
       grind)
    | exact resolve eq1656 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq1656
  have eq9259 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9256
  have eq9261 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq16
    | exact resolve eq16 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9282 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq359 (σ x) (σ y) X0 X1
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq359
    | exact resolve eq359 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9284 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq479 (σ x) (σ y) X0 X1 X2
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq479
    | exact resolve eq479 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9293 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X0)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1338 (σ x) (σ y) X0 X1 X2
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq1338
    | exact resolve eq1338 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9294 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op (σ x) X2)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1338 X0 X1 X2 (σ x) (σ y)
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq1338
    | exact resolve eq1338 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq9295 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1596 (σ x) (σ y)
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq1596
    | exact resolve eq1596 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9327 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9295
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq9295
    | exact resolve eq9295 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9295
  have eq9405 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9282 X0 (M.op X0 x)
       have i₂ := eq9282 X0 x
       grind)
    | exact superpose eq9282 eq9282
    | exact resolve eq9282 eq9282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9452 : (σ (k x x)) = (M.op (σ x) (σ (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9282 (σ x) (σ x)
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq9282
    | exact resolve eq9282 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9636 : (σ (k x x)) = (M.op (σ x) (σ (k x x))) ∨ x = (M.op x y) := by grind
  clear eq9452
  have eq9637 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9405
  have eq11240 : (τ (M.op (σ x) (σ x))) = (k x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1647 x (σ y)
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq1647
    | exact resolve eq1647 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11264 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) (σ X2))) = (k X2 (τ (M.op (σ X2) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1647 X2 X1
       have i₂ := eq9 (σ X2) X1 X0
       grind)
    | exact superpose eq9 eq1647
    | exact resolve eq1647 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11269 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op X0 X1) (σ X2))) = (k X2 (τ (M.op (σ X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1647 X2 X3
       have i₂ := eq359 X0 X1 (σ X2) X3
       grind)
    | exact superpose eq359 eq1647
    | exact resolve eq1647 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11299 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11240
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11240
    | exact resolve eq11240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11240
  have eq11443 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) (σ (τ X2)))) = (τ (k X2 (M.op (σ (τ X2)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (M.op (σ (τ X2)) X1) X2
       have i₂ := eq11264 X0 X1 (τ X2)
       grind)
    | exact superpose eq11264 eq31
    | exact resolve eq31 eq11264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11446 : ∀ X0 X1 X2 : G, (k X2 (σ (τ (M.op (σ (τ X2)) X1)))) = (σ (τ (M.op (M.op X0 X1) (σ (τ X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (τ (M.op (σ (τ X2)) X1))
       have i₂ := eq11264 X0 X1 (τ X2)
       grind)
    | exact superpose eq11264 eq17
    | exact resolve eq17 eq11264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11453 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ (τ X2))) = (k X2 (σ (τ (M.op (σ (τ X2)) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11446 X0 X1 X2
       have i₂ := eq11 (M.op (M.op X0 X1) (σ (τ X2)))
       grind)
    | exact superpose eq11 eq11446
    | exact resolve eq11446 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11446
  have eq11456 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (τ (k X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11443 X0 X1 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11443
    | exact resolve eq11443 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11443
  have eq11497 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ (τ X2))) = (k X2 (M.op (σ (τ X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11453 X0 X1 X2
       have i₂ := eq11 (M.op (σ (τ X2)) X1)
       grind)
    | exact superpose eq11 eq11453
    | exact resolve eq11453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11453
  have eq11500 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (τ (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11456 X0 X1 X2
       have i₂ := eq1596 X2 X1
       grind)
    | exact superpose eq1596 eq11456
    | exact resolve eq11456 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11456
  have eq11524 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11497 X0 X1 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11497
    | exact resolve eq11497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11497
  have eq11602 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq11524 x X3 X0
       have i₂ := eq359 x X3 X0 X1
       grind)
    | exact superpose eq359 eq11524
    | exact resolve eq11524 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11603 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X2 X4)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq11524 x X4 X2
       have i₂ := eq479 x X4 X2 X0 X1
       grind)
    | (have i₁ := eq11524 x X4 X2
       have i₂ := eq479 X0 X1 X2 x X4
       grind)
    | exact superpose eq479 eq11524
    | exact resolve eq11524 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11866 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (τ X2))) = (k X2 (σ (M.op (τ X2) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (M.op (τ X2) X1)
       have i₂ := eq11524 X0 X1 (τ X2)
       grind)
    | exact superpose eq11524 eq17
    | exact resolve eq17 eq11524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12282 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11602 (σ x) X0 (σ y)
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq11602
    | exact resolve eq11602 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12468 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X0 ∨ (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3727 X0 (M.op X0 X2)
       have i₂ := eq11602 X0 X1 X2
       grind)
    | exact superpose eq11602 eq3727
    | (have j0 := eq3727 X0 (M.op X0 X2)
       grind)
    | exact resolve eq3727 eq11602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12619 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (σ (k x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12282 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq12282
    | exact resolve eq12282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12282
  have eq12880 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq11603 X0 X1 (σ x) (σ y)
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq11603
    | exact resolve eq11603 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12881 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (k (σ x) (σ (k x x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq11603 X0 X1 (σ x) (σ x)
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq11603
    | exact resolve eq11603 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13199 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (σ (k x (k x x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq12881 X0 X1
       have i₂ := eq15 x (k x x)
       grind)
    | exact superpose eq15 eq12881
    | exact resolve eq12881 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12881
  have eq13200 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (σ (k x x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq12880 X0 X1
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq12880
    | exact resolve eq12880 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12880
  have eq13682 : ∀ X0 X1 X3 : G, (τ (M.op X0 (M.op X0 X1))) = (τ (M.op X0 (M.op X0 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq11500 x X3 X0
       have i₂ := eq359 x X3 X0 X1
       grind)
    | exact superpose eq359 eq11500
    | exact resolve eq11500 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13783 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X1 X2) X0)) = (τ (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11500 X1 X2 X0
       have i₂ := eq9282 X0 X2
       grind)
    | exact superpose eq9282 eq11500
    | exact resolve eq11500 eq9282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11500
  have eq18352 : ∀ X0 X1 : G, (k x (τ (σ x))) = (τ (M.op (M.op X0 X1) (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq11269 X0 X1 x (σ y)
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq11269
    | exact resolve eq11269 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18382 : ∀ X0 X1 : G, (k x (k x x)) = (τ (M.op (M.op X0 X1) (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq11269 X0 X1 x (σ x)
       have i₂ := eq11299
       grind)
    | exact superpose eq11299 eq11269
    | exact resolve eq11269 eq11299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11269
  have eq18452 : ∀ X1 : G, (k x (k x x)) = (k x (τ (M.op (σ x) X1))) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq18382 x X1
       have i₂ := eq11264 x X1 x
       grind)
    | exact superpose eq11264 eq18382
    | exact resolve eq18382 eq11264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18382
  have eq18459 : ∀ X1 : G, (k x (τ (σ x))) = (k x (τ (M.op (σ x) X1))) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq18352 x X1
       have i₂ := eq11264 x X1 x
       grind)
    | exact superpose eq11264 eq18352
    | exact resolve eq18352 eq11264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11264 eq18352
  have eq18490 : ∀ X1 : G, (k x x) = (k x (τ (M.op (σ x) X1))) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq18459 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18459
    | exact resolve eq18459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18459
  have eq18669 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (τ (σ X2)))) = (σ (k X2 (M.op (τ (σ X2)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op (τ (σ X2)) X1)
       have i₂ := eq11866 X0 X1 (σ X2)
       grind)
    | exact superpose eq11866 eq15
    | exact resolve eq15 eq11866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11866
  have eq18685 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (σ (k X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18669 X0 X1 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18669
    | exact resolve eq18669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18669
  have eq18729 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (σ (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18685 X0 X1 X2
       have i₂ := eq1596 X2 X1
       grind)
    | exact superpose eq1596 eq18685
    | exact resolve eq18685 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18685
  have eq18831 : ∀ X0 X1 X3 : G, (σ (M.op X0 (M.op X0 X1))) = (σ (M.op X0 (M.op X0 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq18729 x X3 X0
       have i₂ := eq359 x X3 X0 X1
       grind)
    | exact superpose eq359 eq18729
    | exact resolve eq18729 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq18729
  have eq23711 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (M.op (M.op X1 X0) X0)) = (k (M.op (M.op X1 X0) X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X0 X0 (M.op X1 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq23712 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op (M.op X1 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23711 X0 X1
       have i₂ := eq728 X0 X0 X1
       grind)
    | exact superpose eq728 eq23711
    | (have j0 := eq23711 X0 X1
       grind)
    | exact resolve eq23711 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23711
  have eq26395 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1693 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq1693
    | (have j0 := eq1693 X0 (τ X1)
       grind)
    | exact resolve eq1693 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq26446 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26395 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq26395
    | (have j0 := eq26395 X0 X1
       grind)
    | exact resolve eq26395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26395
  have eq26463 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26446 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26446
    | (have j0 := eq26446 X0 X1
       grind)
    | exact resolve eq26446 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26446
  have eq26468 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26463 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26463
    | (have j0 := eq26463 X0 X1
       grind)
    | exact resolve eq26463 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26463
  have eq26473 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26468 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq26468
    | (have j0 := eq26468 X0 X1
       grind)
    | exact resolve eq26468 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26468
  have eq26476 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26473 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq26473
    | (have j0 := eq26473 X0 X1
       grind)
    | exact resolve eq26473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26473
  have eq26477 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26476 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26476
    | (have j0 := eq26476 X0 X1
       grind)
    | exact resolve eq26476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26476
  have eq27803 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (M.op (M.op X0 (M.op X0 X1)) X0) X0) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1958 X0 X1 X0 (M.op X0 (M.op X0 X1))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq27804 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op (M.op X0 (M.op X0 X1)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27803 X0 X1
       have i₂ := eq728 X0 (M.op X0 X1) X0
       grind)
    | exact superpose eq728 eq27803
    | (have j0 := eq27803 X0 X1
       grind)
    | exact resolve eq27803 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq27803
  have eq27835 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 (M.op X0 X1))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27804 X0 X1
       have i₂ := eq9 X0 (M.op X0 X1) X0
       grind)
    | exact superpose eq9 eq27804
    | (have j0 := eq27804 X0 X1
       grind)
    | exact resolve eq27804 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27804
  have eq27842 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27835 X0 x
       have i₂ := eq112 X0 X0 x
       grind)
    | exact superpose eq112 eq27835
    | (have j0 := eq27835 X0 x
       grind)
    | exact resolve eq27835 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27835
  have eq35010 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9637 (σ y)
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq9637
    | exact resolve eq9637 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9637
  have eq35354 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq35010
  have eq35404 : (τ (M.op (σ y) (σ x))) = (k y (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1647 y (σ x)
       have i₂ := eq35354
       grind)
    | exact superpose eq35354 eq1647
    | exact resolve eq1647 eq35354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq35455 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1596 (σ y) (σ x)
       have i₂ := eq35354
       grind)
    | exact superpose eq35354 eq1596
    | exact resolve eq1596 eq35354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35495 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9282 (σ y) (σ x)
       have i₂ := eq35354
       grind)
    | exact superpose eq35354 eq9282
    | exact resolve eq9282 eq35354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35548 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq35495
  have eq35567 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35455
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq35455
    | exact resolve eq35455 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35455
  have eq35574 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35404
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35404
    | exact resolve eq35404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35404
  have eq35581 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35354
       have i₂ := eq35567
       grind)
    | exact superpose eq35567 eq35354
    | exact resolve eq35354 eq35567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35567
  have eq35729 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq35581
  have eq35769 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (k X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22 X0 (k y x)
       have i₂ := eq35729
       grind)
    | exact superpose eq35729 eq22
    | exact resolve eq22 eq35729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35729
  have eq35802 : ∀ X0 : G, (k (τ X0) (k y x)) = (k (τ X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq35769 X0
       have i₂ := eq22 X0 x
       grind)
    | exact superpose eq22 eq35769
    | exact resolve eq35769 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35769
  have eq36030 : (k x x) = (k x (k x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18490 (σ x)
       have i₂ := eq11299
       grind)
    | exact superpose eq11299 eq18490
    | exact resolve eq18490 eq11299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11299
  have eq36068 : (k x x) = (k x (k x x)) ∨ x = (M.op x y) := by grind
  clear eq36030
  have eq37375 : (σ (k x x)) = (M.op (σ (k x x)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13200 (σ x) (σ x)
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq13200
    | exact resolve eq13200 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13200
  have eq37647 : (σ (k x x)) = (M.op (σ (k x x)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq37375
  have eq39488 : (τ (M.op (σ x) (σ y))) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35574
       have i₂ := eq35548
       grind)
    | exact superpose eq35548 eq35574
    | exact resolve eq35574 eq35548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35548 eq35574
  have eq39651 : (τ (M.op (σ x) (σ y))) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq39488
  have eq46019 : ∀ X0 : G, (k X0 x) = (k X0 (k y x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq35802 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35802
    | exact resolve eq35802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35802
  have eq46143 : ∀ X0 : G, (k X0 (τ (k y x))) = (τ (k (σ X0) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (k y x)
       have i₂ := eq46019 (σ X0)
       grind)
    | exact superpose eq46019 eq28
    | exact resolve eq28 eq46019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46019
  have eq46161 : ∀ X0 : G, (k X0 (τ (k y x))) = (k X0 (τ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq46143 X0
       have i₂ := eq28 X0 x
       grind)
    | exact superpose eq28 eq46143
    | exact resolve eq46143 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq46143
  have eq48110 : ∀ X0 : G, (τ (k X0 (k y x))) = (k (τ X0) (τ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq31 (k y x) X0
       have i₂ := eq46161 (τ X0)
       grind)
    | exact superpose eq46161 eq31
    | exact resolve eq31 eq46161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46161
  have eq48140 : ∀ X0 : G, (τ (k X0 (k y x))) = (τ (k X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq48110 X0
       have i₂ := eq31 x X0
       grind)
    | exact superpose eq31 eq48110
    | exact resolve eq48110 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48110
  have eq56810 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27842 X0
       have i₂ := eq335 X0 X0 x
       grind)
    | (have i₁ := eq27842 x
       have i₂ := eq335 X0 x x
       grind)
    | exact superpose eq335 eq27842
    | (have j0 := eq27842 X0
       grind)
    | exact resolve eq27842 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq27842
  have eq61262 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op (σ x) X0)) = (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X0) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11524 X1 (M.op (M.op X2 X3) X0) X0
       have i₂ := eq9293 X0 X2 X3
       grind)
    | exact superpose eq9293 eq11524
    | exact resolve eq11524 eq9293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9293 eq11524
  have eq61512 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 (M.op X2 X3))) = (k X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq61262 X0 x X2 X3
       have i₂ := eq110 x (M.op X2 X3) X0 X0
       grind)
    | exact superpose eq110 eq61262
    | exact resolve eq61262 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq61262
  have eq61577 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = (k X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq61512 X0 X2 x
       have i₂ := eq112 X0 X2 x
       grind)
    | exact superpose eq112 eq61512
    | exact resolve eq61512 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq61512
  have eq61769 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 X1) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq9294 X0 X1 (σ y)
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq9294
    | exact resolve eq9294 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9294
  have eq62657 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 X1) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq61769 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61769
  have eq82998 : (τ (M.op (σ x) (σ y))) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13783 (σ y) x x
       have i₂ := eq62657 x x
       grind)
    | exact superpose eq62657 eq13783
    | exact resolve eq13783 eq62657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62657
  have eq83110 : (τ (M.op (σ x) (σ y))) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq82998
  have eq90547 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61577 (σ y) X0
       have i₂ := eq9259
       grind)
    | exact superpose eq9259 eq61577
    | exact resolve eq61577 eq9259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9259
  have eq90658 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9282 X0 x
       have i₂ := eq61577 X0 x
       grind)
    | exact superpose eq61577 eq9282
    | exact resolve eq9282 eq61577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61577
  have eq91263 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq90658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90658
  have eq91280 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq90547 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90547
  have eq91433 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (σ (k y x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq91280 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq91280
    | exact resolve eq91280 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91280
  have eq91486 : (σ (k x x)) = (k (σ x) (σ (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91263 (σ x)
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq91263
    | exact resolve eq91263 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9327
  have eq91487 : (σ (k x x)) = (k (σ (k x x)) (σ (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91263 (σ (k x x))
       have i₂ := eq9636
       grind)
    | exact superpose eq9636 eq91263
    | exact resolve eq91263 eq9636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9636
  have eq91638 : (σ (k x x)) = (k (σ (k x x)) (σ (k x x))) ∨ x = (M.op x y) := by grind
  clear eq91487
  have eq91639 : (σ (k x x)) = (k (σ x) (σ (k x x))) ∨ x = (M.op x y) := by grind
  clear eq91486
  have eq91668 : (σ (k x x)) = (σ (k (k x x) (k x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91638
       have i₂ := eq15 (k x x) (k x x)
       grind)
    | exact superpose eq15 eq91638
    | exact resolve eq91638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91638
  have eq91669 : (σ (k x x)) = (σ (k x (k x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91639
       have i₂ := eq15 x (k x x)
       grind)
    | exact superpose eq15 eq91639
    | exact resolve eq91639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91639
  have eq232092 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (k (σ y) (σ (k y x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq11603 X0 X1 (σ y) (M.op (σ y) x)
       have i₂ := eq91433 x
       grind)
    | exact superpose eq91433 eq11603
    | exact resolve eq11603 eq91433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11603 eq91433
  have eq232531 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (σ (k y (k y x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq232092 X0 X1
       have i₂ := eq15 y (k y x)
       grind)
    | exact superpose eq15 eq232092
    | exact resolve eq232092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232092
  have eq280399 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) = (σ (k (τ X0) (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1689 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq1689
    | (have j0 := eq1689 (τ X0) (τ X1)
       grind)
    | exact resolve eq1689 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1689
  have eq281159 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) = (k X0 (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq280399 X0 X1
       have i₂ := eq17 X0 (τ (k X0 X1))
       grind)
    | exact superpose eq17 eq280399
    | (have j0 := eq280399 X0 X1
       grind)
    | exact resolve eq280399 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq280399
  have eq281279 : ∀ X0 X1 : G, (k X0 (k X0 X1)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq281159 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq281159
    | (have j0 := eq281159 X0 X1
       grind)
    | exact resolve eq281159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281159
  have eq281345 : ∀ X0 X1 : G, (k X0 (k X0 X1)) = (M.op X0 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq281279 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq281279
    | (have j0 := eq281279 X0 X1
       grind)
    | exact resolve eq281279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281279
  have eq281393 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 (k X0 X1)) = (M.op X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq281345 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq281345
    | (have j0 := eq281345 X0 X1
       grind)
    | exact resolve eq281345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281345
  have eq281405 : ∀ X0 X1 : G, (k X0 (k X0 X1)) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq281393 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq281393
    | (have j0 := eq281393 X0 X1
       grind)
    | exact resolve eq281393 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281393
  have eq363057 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3871 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3871
    | (have j0 := eq3871 X1 X2 X2
       grind)
    | exact resolve eq3871 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871
  have eq450867 : (k x (k x x)) = (k x (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18452 (σ y)
       have i₂ := eq39651
       grind)
    | exact superpose eq39651 eq18452
    | exact resolve eq18452 eq39651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18452 eq39651
  have eq450970 : (k x (k x x)) = (k x (k y x)) ∨ x = (M.op x y) := by grind
  clear eq450867
  have eq451096 : (τ (k x x)) = (τ (k x (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48140 x
       have i₂ := eq450970
       grind)
    | exact superpose eq450970 eq48140
    | exact resolve eq48140 eq450970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48140 eq450970
  have eq451153 : (τ (k x x)) = (τ (k x (k x x))) ∨ x = (M.op x y) := by grind
  clear eq451096
  have eq476925 : (τ (M.op (σ x) (σ x))) = (τ (σ (k x (k x x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13783 (σ x) x x
       have i₂ := eq13199 x x
       grind)
    | exact superpose eq13199 eq13783
    | exact resolve eq13783 eq13199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13199
  have eq477855 : (τ (M.op (σ x) (σ x))) = (τ (σ (k x (k x x)))) ∨ x = (M.op x y) := by grind
  clear eq476925
  have eq478056 : (k x (k x x)) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq477855
       have i₂ := eq10 (k x (k x x))
       grind)
    | exact superpose eq10 eq477855
    | exact resolve eq477855 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477855
  have eq478353 : (k x x) = (k x (k x (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18490 (σ x)
       have i₂ := eq478056
       grind)
    | exact superpose eq478056 eq18490
    | exact resolve eq18490 eq478056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18490
  have eq478420 : (k x x) = (k x (k x (k x x))) ∨ x = (M.op x y) := by grind
  clear eq478353
  have eq489496 : (τ (σ x)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq83110
       have i₂ := eq35354
       grind)
    | exact superpose eq35354 eq83110
    | exact resolve eq83110 eq35354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35354 eq83110
  have eq489574 : (τ (σ x)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq489496
  have eq489601 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq489574
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq489574
    | exact resolve eq489574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489574
  have eq520238 : (τ (σ (k x x))) = (k (k x x) (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k (k x x) (k x x))
       have i₂ := eq91668
       grind)
    | exact superpose eq91668 eq10
    | exact resolve eq10 eq91668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91668
  have eq520371 : (k x x) = (k (k x x) (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq520238
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq520238
    | exact resolve eq520238 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520238
  have eq520384 : ∀ X0 : G, (k x x) ≠ (k x x) ∨ (k X0 (k x x)) = (M.op X0 (k x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3999 (k x x) X0
       have i₂ := eq520371
       grind)
    | exact superpose eq520371 eq3999
    | (have j0 := eq3999 (k x x) X0
       grind)
    | (have r₁ := eq3999 (k x x) x
       have r₂ := eq520371
       grind)
    | exact resolve eq3999 eq520371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3999
  have eq520427 : (k x x) ≠ (k x x) ∨ (k x x) = (M.op (k x x) (k x x)) ∨ (k x x) = (M.op (k x x) (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26477 (k x x) (k x x)
       have i₂ := eq520371
       grind)
    | exact superpose eq520371 eq26477
    | (have j0 := eq26477 x (k x x)
       grind)
    | (have r₁ := eq26477 (k x x) (k x x)
       have r₂ := eq520371
       grind)
    | exact resolve eq26477 eq520371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26477 eq520371
  have eq520464 : (k x x) ≠ (k x x) ∨ (k x x) = (M.op (k x x) (k x x)) ∨ x = (M.op x y) := by grind
  clear eq520427
  have eq520465 : (k x x) = (M.op (k x x) (k x x)) ∨ x = (M.op x y) := by grind
  clear eq520464
  have eq520475 : ∀ X0 : G, (k X0 (k x x)) = (M.op X0 (k x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq520384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520384
  have eq520538 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (k x x) X0) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq479 (k x x) (k x x) X0 X1 X2
       have i₂ := eq520465
       grind)
    | exact superpose eq520465 eq479
    | exact resolve eq479 eq520465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq520656 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k x x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9284 X0 (k x x) (k x x)
       have i₂ := eq520465
       grind)
    | exact superpose eq520465 eq9284
    | exact resolve eq9284 eq520465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521147 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k x x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq520656 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520656
  have eq521315 : (k x x) = (M.op (σ x) (k x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq520465
       have i₂ := eq521147 (k x x)
       grind)
    | exact superpose eq521147 eq520465
    | exact resolve eq520465 eq521147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520465
  have eq522324 : (k x x) = (M.op (σ x) (k x x)) ∨ x = (M.op x y) := by grind
  clear eq521315
  have eq522387 : (σ (k x x)) = (M.op (σ x) (k x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12619 (k x x)
       have i₂ := eq522324
       grind)
    | exact superpose eq522324 eq12619
    | exact resolve eq12619 eq522324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12619
  have eq523067 : (σ (k x x)) = (M.op (σ x) (k x x)) ∨ x = (M.op x y) := by grind
  clear eq522387
  have eq523531 : (k x x) = (k x (M.op x (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq478420
       have i₂ := eq520475 x
       grind)
    | exact superpose eq520475 eq478420
    | exact resolve eq478420 eq520475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478420
  have eq523535 : (σ (k x x)) = (σ (M.op x (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91669
       have i₂ := eq520475 x
       grind)
    | exact superpose eq520475 eq91669
    | exact resolve eq91669 eq520475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91669
  have eq523536 : (k x x) = (M.op x (k x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36068
       have i₂ := eq520475 x
       grind)
    | exact superpose eq520475 eq36068
    | exact resolve eq36068 eq520475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36068
  have eq523537 : (k x x) = (M.op x (k x x)) ∨ x = (M.op x y) := by grind
  clear eq523536
  have eq523538 : (σ (k x x)) = (σ (M.op x (k x x))) ∨ x = (M.op x y) := by grind
  clear eq523535
  have eq523542 : (k x x) = (k x (M.op x (k x x))) ∨ x = (M.op x y) := by grind
  clear eq523531
  have eq523555 : (k x x) = (M.op x (M.op x (k x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq523542
       have i₂ := eq1596 x (k x x)
       grind)
    | exact superpose eq1596 eq523542
    | exact resolve eq523542 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523542
  have eq523779 : (M.op x (k x x)) = (M.op (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9282 x (k x x)
       have i₂ := eq523537
       grind)
    | exact superpose eq523537 eq9282
    | exact resolve eq9282 eq523537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523796 : ∀ X0 : G, (k x (k x x)) = (M.op x (M.op x X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11602 x X0 (k x x)
       have i₂ := eq523537
       grind)
    | exact superpose eq523537 eq11602
    | exact resolve eq11602 eq523537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11602
  have eq524237 : (M.op x (k x x)) = (M.op (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq523779
  have eq524315 : (k x x) = (M.op (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq523537
       have i₂ := eq524237
       grind)
    | exact superpose eq524237 eq523537
    | exact resolve eq523537 eq524237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523537
  have eq524925 : (k x x) = (M.op (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq524315
  have eq533463 : (σ (k x x)) = (σ (M.op (σ x) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq523538
       have i₂ := eq524237
       grind)
    | exact superpose eq524237 eq523538
    | exact resolve eq523538 eq524237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523538 eq524237
  have eq533564 : (σ (k x x)) = (σ (M.op (σ x) x)) ∨ x = (M.op x y) := by grind
  clear eq533463
  have eq533785 : ∀ X0 : G, (τ (k x x)) = (τ (M.op x (M.op x X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13682 x (k x x) X0
       have i₂ := eq523555
       grind)
    | exact superpose eq523555 eq13682
    | exact resolve eq13682 eq523555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13682
  have eq533797 : ∀ X0 : G, (σ (k x x)) = (σ (M.op x (M.op x X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18831 x (k x x) X0
       have i₂ := eq523555
       grind)
    | exact superpose eq523555 eq18831
    | exact resolve eq18831 eq523555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18831 eq523555
  have eq549178 : (k x (k x x)) = (M.op (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9282 x x
       have i₂ := eq523796 x
       grind)
    | exact superpose eq523796 eq9282
    | exact resolve eq9282 eq523796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9282 eq523796
  have eq549939 : (k x (k x x)) = (M.op (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq549178
  have eq561448 : (k x x) = (σ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq522324
       have i₂ := eq523067
       grind)
    | exact superpose eq523067 eq522324
    | exact resolve eq522324 eq523067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522324
  have eq562149 : (k x x) = (σ (k x x)) ∨ x = (M.op x y) := by grind
  clear eq561448
  have eq562256 : (k x x) = (M.op (k x x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37647
       have i₂ := eq562149
       grind)
    | exact superpose eq562149 eq37647
    | exact resolve eq37647 eq562149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37647
  have eq562288 : (k x x) = (τ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq562149
       grind)
    | exact superpose eq562149 eq10
    | exact resolve eq10 eq562149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562149
  have eq562389 : (k x x) = (M.op (k x x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq562256
  have eq562474 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq520538 (σ x) X0 X1
       have i₂ := eq562389
       grind)
    | exact superpose eq562389 eq520538
    | exact resolve eq520538 eq562389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520538
  have eq562475 : (M.op (σ x) (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq521147 (σ x)
       have i₂ := eq562389
       grind)
    | exact superpose eq562389 eq521147
    | exact resolve eq521147 eq562389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521147 eq562389
  have eq563153 : (M.op (σ x) (σ x)) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq562475
  have eq563154 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (k x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq562474 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562474
  have eq563224 : (k x (k x x)) = (τ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq478056
       have i₂ := eq563153
       grind)
    | exact superpose eq563153 eq478056
    | exact resolve eq478056 eq563153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478056 eq563153
  have eq563952 : (k x (k x x)) = (τ (k x x)) ∨ x = (M.op x y) := by grind
  clear eq563224
  have eq564347 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (k x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq563154 x X0
       have i₂ := eq9 (σ x) X0 x
       grind)
    | exact superpose eq9 eq563154
    | exact resolve eq563154 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563154
  have eq570268 : (τ (k x x)) = (τ (τ (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq451153
       have i₂ := eq563952
       grind)
    | exact superpose eq563952 eq451153
    | exact resolve eq451153 eq563952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451153
  have eq570272 : (τ (k x x)) = (M.op (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq549939
       have i₂ := eq563952
       grind)
    | exact superpose eq563952 eq549939
    | exact resolve eq549939 eq563952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549939
  have eq570273 : (τ (k x x)) = (M.op x (k x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq520475 x
       have i₂ := eq563952
       grind)
    | exact superpose eq563952 eq520475
    | exact resolve eq520475 eq563952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520475 eq563952
  have eq570349 : (τ (k x x)) = (M.op x (k x x)) ∨ x = (M.op x y) := by grind
  clear eq570273
  have eq570350 : (τ (k x x)) = (M.op (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq570272
  have eq570354 : (τ (k x x)) = (τ (τ (k x x))) ∨ x = (M.op x y) := by grind
  clear eq570268
  have eq570416 : (k x x) = (σ (M.op (σ x) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (k x x)
       have i₂ := eq570350
       grind)
    | exact superpose eq570350 eq11
    | exact resolve eq11 eq570350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570752 : (τ (k x x)) = (τ (M.op x (τ (k x x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq533785 (k x x)
       have i₂ := eq570349
       grind)
    | exact superpose eq570349 eq533785
    | exact resolve eq533785 eq570349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533785
  have eq571383 : (τ (k x x)) = (τ (M.op x (τ (k x x)))) ∨ x = (M.op x y) := by grind
  clear eq570752
  have eq572703 : (M.op (σ x) x) = (τ (M.op (σ x) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq570354
       have i₂ := eq570350
       grind)
    | exact superpose eq570350 eq570354
    | exact resolve eq570354 eq570350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570354
  have eq572767 : (M.op (σ x) x) = (τ (M.op (σ x) x)) ∨ x = (M.op x y) := by grind
  clear eq572703
  have eq574752 : (M.op (σ x) x) = (σ (M.op (σ x) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (M.op (σ x) x)
       have i₂ := eq572767
       grind)
    | exact superpose eq572767 eq11
    | exact resolve eq11 eq572767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572767
  have eq574960 : (σ (k x x)) = (M.op (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq533564
       have i₂ := eq574752
       grind)
    | exact superpose eq574752 eq533564
    | exact resolve eq533564 eq574752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533564 eq574752
  have eq575060 : (σ (k x x)) = (M.op (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq574960
  have eq586969 : (k x x) = (M.op (σ x) (σ (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq564347 (k x x)
       have i₂ := eq523067
       grind)
    | exact superpose eq523067 eq564347
    | exact resolve eq564347 eq523067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523067 eq564347
  have eq588053 : (k x x) = (M.op (σ x) (σ (k x x))) ∨ x = (M.op x y) := by grind
  clear eq586969
  have eq597976 : (k x x) = (k (σ (k x x)) (k x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91263 (σ (k x x))
       have i₂ := eq588053
       grind)
    | exact superpose eq588053 eq91263
    | exact resolve eq91263 eq588053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91263 eq588053
  have eq598686 : (k x x) = (k (σ (k x x)) (k x x)) ∨ x = (M.op x y) := by grind
  clear eq597976
  have eq754991 : (k x x) = (τ (M.op x (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq571383
       have i₂ := eq562288
       grind)
    | exact superpose eq562288 eq571383
    | exact resolve eq571383 eq562288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571383
  have eq755065 : (k x x) = (τ (M.op x (k x x))) ∨ x = (M.op x y) := by grind
  clear eq754991
  have eq755085 : (k x x) = (τ (τ (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq755065
       have i₂ := eq570349
       grind)
    | exact superpose eq570349 eq755065
    | exact resolve eq755065 eq570349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570349
  have eq755099 : (σ (k x x)) = (M.op x (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (M.op x (k x x))
       have i₂ := eq755065
       grind)
    | exact superpose eq755065 eq11
    | exact resolve eq11 eq755065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755065
  have eq755168 : (k x x) = (τ (τ (k x x))) ∨ x = (M.op x y) := by grind
  clear eq755085
  have eq758129 : (σ (k x x)) = (τ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (τ (k x x))
       have i₂ := eq755168
       grind)
    | exact superpose eq755168 eq11
    | exact resolve eq11 eq755168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755168
  have eq758502 : (σ (k x x)) = (σ (M.op x (σ (k x x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq533797 (k x x)
       have i₂ := eq755099
       grind)
    | exact superpose eq755099 eq533797
    | exact resolve eq533797 eq755099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533797 eq755099
  have eq759187 : (σ (k x x)) = (σ (M.op x (σ (k x x)))) ∨ x = (M.op x y) := by grind
  clear eq758502
  have eq895571 : (τ (σ (k x x))) ≠ (τ (k x x)) ∨ (τ (σ (k x x))) = (M.op (τ (σ (k x x))) (τ (k x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3729 (σ (k x x)) (k x x)
       have i₂ := eq598686
       grind)
    | exact superpose eq598686 eq3729
    | (have j0 := eq3729 (σ (k x x)) (k x x)
       grind)
    | exact resolve eq3729 eq598686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729 eq598686
  have eq895670 : (k x x) ≠ (τ (k x x)) ∨ (τ (σ (k x x))) = (M.op (τ (σ (k x x))) (τ (k x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq895571
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq895571
    | exact resolve eq895571 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895571
  have eq895675 : (τ (σ (k x x))) = (M.op (τ (σ (k x x))) (τ (k x x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq895670
       have r₂ := eq562288
       grind)
    | exact resolve eq895670 eq562288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562288 eq895670
  have eq895676 : (k x x) = (M.op (k x x) (τ (k x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq895675
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq895675
    | exact resolve eq895675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895675
  have eq910915 : (k x x) = (M.op (k x x) (σ (k x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq895676
       have i₂ := eq758129
       grind)
    | exact superpose eq758129 eq895676
    | exact resolve eq895676 eq758129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758129 eq895676
  have eq911696 : (k x x) = (M.op (k x x) (σ (k x x))) ∨ x = (M.op x y) := by grind
  clear eq910915
  have eq923541 : (M.op (σ x) x) = (σ (M.op x (M.op (σ x) x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq759187
       have i₂ := eq575060
       grind)
    | exact superpose eq575060 eq759187
    | exact resolve eq759187 eq575060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575060 eq759187
  have eq923701 : (M.op (σ x) x) = (σ (M.op x (M.op (σ x) x))) ∨ x = (M.op x y) := by grind
  clear eq923541
  have eq2621644 : (τ (M.op (σ x) (σ y))) = (τ (σ (k y (k y x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13783 (σ y) x x
       have i₂ := eq232531 x x
       grind)
    | exact superpose eq232531 eq13783
    | exact resolve eq13783 eq232531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13783
  have eq2623780 : (τ (M.op (σ x) (σ y))) = (τ (σ (k y (k y x)))) ∨ x = (M.op x y) := by grind
  clear eq2621644
  have eq2624447 : (τ (M.op (σ x) (σ y))) = (k y (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2623780
       have i₂ := eq10 (k y (k y x))
       grind)
    | exact superpose eq10 eq2623780
    | exact resolve eq2623780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623780
  have eq2625891 : x = (k y (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq489601
       have i₂ := eq2624447
       grind)
    | exact superpose eq2624447 eq489601
    | exact resolve eq489601 eq2624447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489601 eq2624447
  have eq2626026 : x = (k y (k y x)) ∨ x = (M.op x y) := by grind
  clear eq2625891
  have eq2626040 : x = (M.op y (k y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2626026
       have i₂ := eq281405 y x
       grind)
    | exact superpose eq281405 eq2626026
    | (have j1 := eq281405 x y
       grind)
    | exact resolve eq2626026 eq281405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281405
  have eq2626045 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 X1) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq232531 X0 X1
       have i₂ := eq2626026
       grind)
    | exact superpose eq2626026 eq232531
    | exact resolve eq232531 eq2626026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232531
  have eq2626053 : x = (k y (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq363057 y y x
       have i₂ := eq2626026
       grind)
    | exact superpose eq2626026 eq363057
    | (have j0 := eq363057 x y x
       grind)
    | exact resolve eq363057 eq2626026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363057 eq2626026
  have eq2626256 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 X1) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq2626045 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626045
  have eq2626309 : x = (M.op y (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2626053
       have i₂ := eq1596 y x
       grind)
    | exact superpose eq1596 eq2626053
    | exact resolve eq2626053 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596 eq2626053
  have eq2828113 : x = (k x y) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56810 y x
       have i₂ := eq2626309
       grind)
    | exact superpose eq2626309 eq56810
    | (have j0 := eq56810 y x
       grind)
    | exact resolve eq56810 eq2626309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56810 eq2626309
  have eq2829637 : y = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq3727 y y
       grind)
    | (have r₁ := eq2828113
       have r₂ := eq3727 x y
       grind)
    | exact resolve eq2828113 eq3727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3727 eq2828113
  have eq2830156 : ∀ X0 : G, y ≠ (M.op y y) ∨ y = (M.op y (M.op y X0)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12468 y y X0
       have i₂ := eq2829637
       grind)
    | exact superpose eq2829637 eq12468
    | (have j0 := eq12468 y x X0
       grind)
    | exact resolve eq12468 eq2829637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12468
  have eq2831109 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2830156 X0
       grind)
    | (have r₁ := eq2830156 X0
       have r₂ := eq2829637
       grind)
    | exact resolve eq2830156 eq2829637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829637 eq2830156
  have eq2879169 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2831109 (k y x)
       have i₂ := eq2626040
       grind)
    | exact superpose eq2626040 eq2831109
    | exact resolve eq2831109 eq2626040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626040 eq2831109
  have eq2880829 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq2879169
  have eq2881608 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9284 X0 y x
       have i₂ := eq2880829
       grind)
    | exact superpose eq2880829 eq9284
    | exact resolve eq9284 eq2880829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9284
  have eq2882405 : (σ x) = (M.op y (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2626256 y x
       have i₂ := eq2880829
       grind)
    | exact superpose eq2880829 eq2626256
    | exact resolve eq2626256 eq2880829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626256
  have eq2882410 : (σ x) = (M.op y (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2882405
  have eq2882456 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2881608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2881608
  have eq2896871 : (k x x) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq570416
       have i₂ := eq2882456 x
       grind)
    | exact superpose eq2882456 eq570416
    | exact resolve eq570416 eq2882456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570416 eq2882456
  have eq2899106 : (k x x) = (σ (M.op y x)) ∨ x = (M.op x y) := by grind
  clear eq2896871
  have eq2999117 : (σ y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2899106
       have i₂ := eq2880829
       grind)
    | exact superpose eq2880829 eq2899106
    | exact resolve eq2899106 eq2880829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2880829 eq2899106
  have eq2999568 : (σ y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq2999117
  have eq2999699 : (τ (σ y)) = (M.op (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq570350
       have i₂ := eq2999568
       grind)
    | exact superpose eq2999568 eq570350
    | exact resolve eq570350 eq2999568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570350 eq2999568
  have eq3000995 : (τ (σ y)) = (M.op (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq2999699
  have eq3001369 : y = (M.op (σ x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3000995
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3000995
    | exact resolve eq3000995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3000995
  have eq3010061 : y = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq524925
       have i₂ := eq3001369
       grind)
    | exact superpose eq3001369 eq524925
    | exact resolve eq524925 eq3001369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524925
  have eq3010147 : y = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq923701
       have i₂ := eq3001369
       grind)
    | exact superpose eq3001369 eq923701
    | exact resolve eq923701 eq3001369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923701 eq3001369
  have eq3011485 : y = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3010147
  have eq3011571 : y = (k x x) ∨ x = (M.op x y) := by grind
  clear eq3010061
  have eq3012258 : y = (M.op y (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq911696
       have i₂ := eq3011571
       grind)
    | exact superpose eq3011571 eq911696
    | exact resolve eq911696 eq3011571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911696 eq3011571
  have eq3013046 : y = (M.op y (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3012258
  have eq3047271 : y ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9261
       have i₂ := eq3011485
       grind)
    | exact superpose eq3011485 eq9261
    | exact resolve eq9261 eq3011485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9261 eq3011485
  have eq3047719 : y ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq3047271
  have eq3047846 : y = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2882410
       have i₂ := eq3013046
       grind)
    | exact superpose eq3013046 eq2882410
    | exact resolve eq2882410 eq3013046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882410 eq3013046
  have eq3049019 : y = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3047846
  have eq3049232 : x = (M.op x y) := by
    first
    | (have r₁ := eq3049019
       have r₂ := eq3047719
       grind)
    | exact resolve eq3049019 eq3047719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047719 eq3049019
  have eq3049311 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq3049232
       grind)
    | exact superpose eq3049232 eq9
    | exact resolve eq9 eq3049232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3049316 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x y X0 X1
       have i₂ := eq3049232
       grind)
    | exact superpose eq3049232 eq53
    | exact resolve eq53 eq3049232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3058277 : (M.op y (M.op y y)) = (k (M.op x y) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq23712 y x
       have i₂ := eq3049316 y x
       grind)
    | exact superpose eq3049316 eq23712
    | (have j0 := eq23712 y x
       grind)
    | exact resolve eq23712 eq3049316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23712 eq3049316
  have eq3061928 : (k x y) = (M.op y (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3058277
       have i₂ := eq3049232
       grind)
    | exact superpose eq3049232 eq3058277
    | exact resolve eq3058277 eq3049232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3058277
  have eq3062574 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3061928
       have i₂ := eq3049311 y
       grind)
    | exact superpose eq3049311 eq3061928
    | exact resolve eq3061928 eq3049311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049311 eq3061928
  have eq3062925 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq3062574
       have r₂ := eq12 x y
       grind)
    | exact resolve eq3062574 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3062574
  have eq3063058 : x = (k x y) := by
    first
    | (have i₁ := eq3062925
       have i₂ := eq3049232
       grind)
    | exact superpose eq3049232 eq3062925
    | exact resolve eq3062925 eq3049232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3062925
  have eq3063547 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1687 x y
       have i₂ := eq3063058
       grind)
    | exact superpose eq3063058 eq1687
    | (have j0 := eq1687 x y
       grind)
    | exact resolve eq1687 eq3063058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687 eq3063058
  have eq3063772 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3063547
  have eq3065122 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3063772
       grind)
    | exact superpose eq3063772 eq16
    | exact resolve eq16 eq3063772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063772
  have eq3066527 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3065122
       have i₂ := eq3049232
       grind)
    | exact superpose eq3049232 eq3065122
    | exact resolve eq3065122 eq3049232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049232 eq3065122
  have eq3066528 : False := by grind
  exact eq3066528

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_y_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq122
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq125
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq125
    | exact resolve eq125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq83
    | (have j0 := eq83 (σ x) (σ y)
       grind)
    | exact resolve eq83 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq193
    | exact resolve eq193 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq197 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq194
       have r₂ := eq27
       grind)
    | exact resolve eq194 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq199 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq197
    | exact resolve eq197 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq253 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq259 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq199 eq51
    | exact resolve eq51 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq199
  have eq266 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq259 eq14
    | exact resolve eq14 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq286 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq266 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq293 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq286 X0
       have j1 := eq83 X0 (σ y)
       grind)
    | (have r₁ := eq286 X0
       have r₂ := eq83 X0 (σ y)
       grind)
    | exact resolve eq286 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq293 eq126
    | exact resolve eq126 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq293
  have eq363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq360
  have eq366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq363
    | exact resolve eq363 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq368 : y = (M.op x y) := by
    first
    | (have r₁ := eq366
       have r₂ := eq27
       grind)
    | exact resolve eq366 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq403 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq368 eq20
    | exact resolve eq20 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : y = (M.op y y) := by
    first
    | exact superpose eq368 eq253
    | exact resolve eq253 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq368
  have eq416 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq403
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq403
    | exact resolve eq403 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq403
  have eq419 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq416 eq26
    | exact resolve eq26 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq453 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq410
       grind)
    | exact superpose eq410 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq459 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq453 X0
       have j1 := eq83 X0 y
       grind)
    | (have r₁ := eq453 X0
       have r₂ := eq83 X0 y
       grind)
    | exact resolve eq453 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq538 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq459 x
       grind)
    | exact superpose eq459 eq44
    | exact resolve eq44 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq459
  have eq543 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq416 eq538
    | exact resolve eq538 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq538
  have eq546 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq543
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq543
    | exact resolve eq543 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq543
  have eq548 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq546
    | exact resolve eq546 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq546
  have eq552 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq548 eq83
    | (have j0 := eq83 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq83 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq548
  have eq553 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq552
  have eq555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq419 eq553
    | exact resolve eq553 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq553
  have eq558 : False := by grind
  exact eq558

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pxy_pyx_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X1 (M.op X2 X0))) X3 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X0 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X1 (M.op X2 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X1 (M.op X1 (M.op X2 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq12
    | (have r₁ := eq12 (M.op X1 X0) X0
       have r₂ := eq22 X0 X1
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq43
    | exact resolve eq43 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X1 (M.op X2 (τ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op X1 (M.op X2 (τ X0))))
       have i₂ := eq34 (τ X0) X1 X2
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X1 (M.op X2 (τ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq101
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq132 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (M.op X1 (M.op X2 (τ (τ X0)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (σ (M.op X1 (M.op X1 (M.op X2 (τ (τ X0))))))
       have i₂ := eq104 (τ X0) X1 X2
       grind)
    | exact superpose eq104 eq18
    | exact resolve eq18 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op X1 (M.op X1 (M.op X2 (τ (τ X0)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq132 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq132
    | exact resolve eq132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq188 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op X3 (M.op X3 X2)) (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X3 (M.op X3 X2)) X4 (M.op X0 (M.op X0 (M.op X1 X2)))
       have i₂ := eq20 X2 X0 X1 X3
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq237 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq50
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op (M.op X1 (M.op X2 (σ X0))) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X0) X1 X2
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq21
    | (have j1 := eq50 X0 X0
       grind)
    | exact resolve eq21 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq50
  have eq259 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op (M.op X1 (M.op X2 (σ X0))) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq245 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq911 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op X0 (τ X1)) (τ X2)) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (M.op X0 (τ X1)) X2
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq43
    | (have j1 := eq48 X0 X1
       grind)
    | exact resolve eq43 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq48
  have eq920 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (k (M.op X0 (τ X1)) (τ X2)) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq911 X0 X1 X2
       have i₂ := eq66 X0 X1 X2
       grind)
    | exact superpose eq66 eq911
    | (have j0 := eq911 X0 X1 X2
       grind)
    | exact resolve eq911 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq911
  have eq1966 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op X2 (M.op X2 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188 (M.op X0 X1) X0 X1 X2 (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq188
    | exact resolve eq188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq2032 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1966 X0 (M.op X1 (M.op X2 X1)) X1
       have i₂ := eq9 X1 X1 X2
       grind)
    | exact superpose eq9 eq1966
    | exact resolve eq1966 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966
  have eq3126 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ (τ X0)))) = (M.op (M.op X1 (M.op X2 (σ (τ X0)))) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259 (τ X0) X1 X2
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq259
    | (have j0 := eq259 (τ X0) X1 X2
       grind)
    | exact resolve eq259 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq259
  have eq3175 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3126 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3126
    | (have j0 := eq3126 X0 X1 X2
       grind)
    | exact resolve eq3126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3126
  have eq3182 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3175 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3175
    | (have j0 := eq3175 X0 X1 X2
       grind)
    | exact resolve eq3175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3175
  have eq14876 : ∀ X0 X1 X2 X3 : G, (k X2 X2) = (k (k X2 X2) (M.op X3 (M.op X3 (M.op X0 (M.op X1 X2))))) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34 (k X2 X2) X3 (M.op X0 (M.op X1 X2))
       have i₂ := eq3182 X2 X0 X1
       grind)
    | exact superpose eq3182 eq34
    | (have j1 := eq3182 X2 X1 X2
       grind)
    | exact resolve eq34 eq3182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3182
  have eq33220 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14876 X0 x X0 X0
       have i₂ := eq2032 X0 x X0
       grind)
    | exact superpose eq2032 eq14876
    | (have j0 := eq14876 X0 x X0 x
       grind)
    | exact resolve eq14876 eq2032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032 eq14876
  have eq47632 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33220 (τ X0)
       have i₂ := eq920 (τ X0) X0 X0
       grind)
    | exact superpose eq920 eq33220
    | (have j0 := eq33220 (τ X0)
       have j1 := eq920 (τ X0) X0 x
       grind)
    | exact resolve eq33220 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq33220
  have eq47745 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq47632 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47632
  have eq47823 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq47745 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq47745
    | (have j0 := eq47745 X0
       grind)
    | exact resolve eq47745 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47745
  have eq47906 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47823 X0
       have i₂ := eq33 (τ X0) (τ X0)
       grind)
    | exact superpose eq33 eq47823
    | (have j0 := eq47823 X0
       grind)
    | exact resolve eq47823 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47823
  have eq47964 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq47906 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47906
    | exact resolve eq47906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48037 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 (τ X0) (τ X0)
       have i₂ := eq47906 X0
       grind)
    | exact superpose eq47906 eq33
    | (have j1 := eq47906 X0
       grind)
    | exact resolve eq33 eq47906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq48147 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq47906 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47906
  have eq48151 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48037 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq48037
    | (have j0 := eq48037 X0
       grind)
    | exact resolve eq48037 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq48037
  have eq48169 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47964 X0
       have i₂ := eq30 (σ X0) X0
       grind)
    | exact superpose eq30 eq47964
    | (have j0 := eq47964 X0
       grind)
    | exact resolve eq47964 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq47964
  have eq48170 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq48151 X0
       have j1 := eq48147 X0
       grind)
    | (have r₁ := eq48151 X0
       have r₂ := eq48147 X0
       grind)
    | exact resolve eq48151 eq48147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48147 eq48151
  have eq48182 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48169 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48169
    | (have j0 := eq48169 X0
       grind)
    | exact resolve eq48169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48169
  have eq48189 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48182 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq48182 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq48182 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48182
  have eq48322 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq48189 (σ X0)
       grind)
    | exact superpose eq48189 eq15
    | exact resolve eq15 eq48189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48426 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48322 X0
       have i₂ := eq48189 X0
       grind)
    | exact superpose eq48189 eq48322
    | exact resolve eq48322 eq48189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48322
  have eq49104 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (M.op X1 (τ (k X0 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1 (τ X0)
       have i₂ := eq48170 X0
       grind)
    | exact superpose eq48170 eq104
    | exact resolve eq104 eq48170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq49113 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 (M.op X1 (τ (k (τ X0) (τ X0)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X1 (τ (τ X0))
       have i₂ := eq48170 (τ X0)
       grind)
    | exact superpose eq48170 eq135
    | exact resolve eq135 eq48170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq49423 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49113 X0 X1
       have i₂ := eq48189 (τ X0)
       grind)
    | exact superpose eq48189 eq49113
    | exact resolve eq49113 eq48189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49113
  have eq49432 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (M.op X1 (τ (M.op X0 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49104 X0 X1
       have i₂ := eq48189 X0
       grind)
    | exact superpose eq48189 eq49104
    | exact resolve eq49104 eq48189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49104
  have eq49483 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (k X0 X0)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49423 X0 X1
       have i₂ := eq48170 X0
       grind)
    | exact superpose eq48170 eq49423
    | exact resolve eq49423 eq48170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49423
  have eq49525 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (M.op X0 X0)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49483 X0 X1
       have i₂ := eq48189 X0
       grind)
    | exact superpose eq48189 eq49483
    | exact resolve eq49483 eq48189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49483
  have eq49694 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) (σ X0)
       have i₂ := eq48426 X0
       grind)
    | exact superpose eq48426 eq22
    | exact resolve eq22 eq48426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52593 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) ∨ (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq237 X0 (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))) X2
       have i₂ := eq49432 (τ X0) X1
       grind)
    | exact superpose eq49432 eq237
    | (have j0 := eq237 X0 (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))) X2
       grind)
    | exact resolve eq237 eq49432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq49432
  have eq52665 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (k X0 X0)))))))) (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) ∨ (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52593 X0 X1 X2
       have i₂ := eq48170 X0
       grind)
    | exact superpose eq48170 eq52593
    | (have j0 := eq52593 X0 X1 X2
       grind)
    | exact resolve eq52593 eq48170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52593
  have eq52761 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (M.op X0 X0)))))))) (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) ∨ (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52665 X0 X1 X2
       have i₂ := eq48189 X0
       grind)
    | exact superpose eq48189 eq52665
    | (have j0 := eq52665 X0 X1 X2
       grind)
    | exact resolve eq52665 eq48189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52665
  have eq52830 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (σ (k (τ X0) X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) ∨ (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52761 X0 X1 X2
       have i₂ := eq49525 X0 X1
       grind)
    | exact superpose eq49525 eq52761
    | (have j0 := eq52761 X0 X1 X2
       grind)
    | exact resolve eq52761 eq49525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52761
  have eq52875 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) ∨ (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52830 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq52830
    | (have j0 := eq52830 X0 X1 X2
       grind)
    | exact resolve eq52830 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52830
  have eq52895 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (k X0 X0)))))))) ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52875 X0 X1 X2
       have i₂ := eq48170 X0
       grind)
    | exact superpose eq48170 eq52875
    | (have j0 := eq52875 X0 X1 X2
       grind)
    | exact resolve eq52875 eq48170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52875
  have eq52902 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (M.op X0 X0)))))))) ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52895 X0 X1 X2
       have i₂ := eq48189 X0
       grind)
    | exact superpose eq48189 eq52895
    | (have j0 := eq52895 X0 X1 X2
       grind)
    | exact resolve eq52895 eq48189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52895
  have eq52906 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X2)) = X0 ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52902 X0 X1 X2
       have i₂ := eq49525 X0 X1
       grind)
    | exact superpose eq49525 eq52902
    | (have j0 := eq52902 X0 X1 X2
       grind)
    | exact resolve eq52902 eq49525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52902
  have eq52908 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = X0 ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (M.op (τ X0) (τ X0)))))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52906 X0 X1 X2
       have i₂ := eq48426 X2
       grind)
    | exact superpose eq48426 eq52906
    | (have j0 := eq52906 X0 X1 X2
       grind)
    | exact resolve eq52906 eq48426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48426 eq52906
  have eq52910 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (k X0 X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (k X0 X0)))))))) (σ X2)) ∨ (σ (M.op X2 X2)) = X0 ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52908 X0 X1 X2
       have i₂ := eq48170 X0
       grind)
    | exact superpose eq48170 eq52908
    | (have j0 := eq52908 X0 X1 X2
       grind)
    | exact resolve eq52908 eq48170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52908
  have eq52912 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (M.op X0 X0)))))))) = (M.op (k X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (M.op X0 X0)))))))) (σ X2)) ∨ (σ (M.op X2 X2)) = X0 ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52910 X0 X1 X2
       have i₂ := eq48189 X0
       grind)
    | exact superpose eq48189 eq52910
    | (have j0 := eq52910 X0 X1 X2
       grind)
    | exact resolve eq52910 eq48189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52910
  have eq52913 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = X0 ∨ (σ (M.op X2 X2)) = X0 ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq52912 X0 x X2
       have i₂ := eq49525 X0 x
       grind)
    | exact superpose eq49525 eq52912
    | (have j0 := eq52912 X0 x X2
       grind)
    | exact resolve eq52912 eq49525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49525 eq52912
  have eq52914 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (σ (M.op X2 X2)) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq52913 X0 X2
       have j1 := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq52913 X0 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq52913 (M.op (σ (M.op X2 X2)) x) X2
       have r₂ := eq12 (σ (M.op X2 X2)) x
       grind)
    | exact resolve eq52913 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52913
  have eq65347 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52914 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52914
    | (have j0 := eq52914 X1 (τ X0)
       grind)
    | exact resolve eq52914 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65508 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq52914 (σ X0) X1
       grind)
    | exact superpose eq52914 eq15
    | (have j1 := eq52914 (σ X0) X1
       grind)
    | exact resolve eq15 eq52914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52914
  have eq65727 : ∀ X0 X1 : G, (σ (τ (k X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65347 X0 X1
       have i₂ := eq48170 X0
       grind)
    | exact superpose eq48170 eq65347
    | (have j0 := eq65347 X0 X1
       grind)
    | exact resolve eq65347 eq48170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48170 eq65347
  have eq65824 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65727 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq65727
    | (have j0 := eq65727 X0 X1
       grind)
    | exact resolve eq65727 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65727
  have eq65868 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65824 X0 X1
       have i₂ := eq48189 X0
       grind)
    | exact superpose eq48189 eq65824
    | (have j0 := eq65824 X0 X1
       grind)
    | exact resolve eq65824 eq48189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48189 eq65824
  have eq66251 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq65868 X1 (τ X0)
       grind)
    | exact superpose eq65868 eq18
    | (have j1 := eq65868 X1 (τ X0)
       grind)
    | exact resolve eq18 eq65868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq65868
  have eq71433 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66251 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66251
    | exact resolve eq66251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66251
  have eq71663 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq71433 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq71433
    | (have j0 := eq71433 X0 X1
       grind)
    | exact resolve eq71433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71433
  have eq85881 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65508 x y
       grind)
    | exact superpose eq65508 eq16
    | (have j1 := eq65508 x y
       grind)
    | exact resolve eq16 eq65508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65508
  have eq86483 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85881
       have i₂ := eq71663 x y
       grind)
    | exact superpose eq71663 eq85881
    | (have j1 := eq71663 x y
       grind)
    | (have r₁ := eq85881
       have r₂ := eq71663 x y
       grind)
    | exact resolve eq85881 eq71663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71663 eq85881
  have eq86486 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq86483
  have eq86915 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq86486
       grind)
    | exact superpose eq86486 eq10
    | exact resolve eq10 eq86486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86486
  have eq87047 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86915
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq86915
    | exact resolve eq86915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86915
  have eq87048 : x = (M.op y y) := by grind
  clear eq87047
  have eq87127 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49694 y
       have i₂ := eq87048
       grind)
    | exact superpose eq87048 eq49694
    | exact resolve eq49694 eq87048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49694
  have eq87147 : x = (M.op x y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq87048
       grind)
    | exact superpose eq87048 eq22
    | exact resolve eq22 eq87048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq87048
  have eq89300 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq87127
       grind)
    | exact superpose eq87127 eq16
    | exact resolve eq16 eq87127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87127
  have eq89554 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq89300
       have i₂ := eq87147
       grind)
    | exact superpose eq87147 eq89300
    | exact resolve eq89300 eq87147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87147 eq89300
  have eq89555 : False := by grind
  exact eq89555

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pyy_pxx_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  clear eq22
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
  clear eq35
  have eq50 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y ≠ (M.op x y) ∨ (k x y) = (M.op y y) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq36
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82
    | exact resolve eq82 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq91 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k x y) = (M.op x x) := by
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
  clear eq18
  have eq111 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq113 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq113 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq113 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq43
    | exact resolve eq43 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq118 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq74
    | exact resolve eq74 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq121 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq114 sF3
       grind)
    | exact superpose eq114 eq118
    | exact resolve eq118 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq114 sF2
       grind)
    | exact superpose eq114 eq117
    | exact resolve eq117 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq127 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq103
       have i₂ := eq114 sF3
       grind)
    | exact superpose eq114 eq103
    | exact resolve eq103 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq127
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq127
    | exact resolve eq127 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq127
  have eq254 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq261 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq9065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9066 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq9065
    | exact resolve eq9065 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9065
  have eq9077 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9066
       have r₂ := eq27
       grind)
    | exact resolve eq9066 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9066
  have eq9081 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq9077
    | exact resolve eq9077 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9077
  have eq9083 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq9081
    | exact resolve eq9081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9081
  have eq9567 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9083 eq111
    | (have r₁ := eq111
       have r₂ := eq9083
       grind)
    | exact resolve eq111 eq9083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9083
  have eq9603 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq9567
  have eq9604 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq9603
  have eq9632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9604 eq92
    | exact resolve eq92 eq9604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9604
  have eq9642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9632
  have eq9644 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9642
       have r₂ := eq27
       grind)
    | exact resolve eq9642 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9642
  have eq9646 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq9644
       grind)
    | exact superpose eq9644 eq110
    | (have r₁ := eq110
       have r₂ := eq9644
       grind)
    | exact resolve eq110 eq9644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9647 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq9644
       grind)
    | exact superpose eq9644 eq122
    | exact resolve eq122 eq9644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq9644
  have eq9682 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9646
  have eq9683 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9682
  have eq9693 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9647
    | exact resolve eq9647 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9647
  have eq9717 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq9683
       grind)
    | exact superpose eq9683 eq44
    | exact resolve eq44 eq9683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9683
  have eq9735 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9717
    | exact resolve eq9717 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9717
  have eq9842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9735 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq9735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9735
  have eq9845 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9842
    | exact resolve eq9842 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9842
  have eq9856 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9845
       have r₂ := eq27
       grind)
    | exact resolve eq9845 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9845
  have eq9860 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9856
    | exact resolve eq9856 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9856
  have eq9862 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9860
    | exact resolve eq9860 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9860
  have eq9863 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9862
  have eq10057 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9863 eq9693
    | exact resolve eq9693 eq9863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9693 eq9863
  have eq10088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10057
  have eq10095 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10088
       have r₂ := eq27
       grind)
    | exact resolve eq10088 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10088
  have eq10097 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10095 eq27
    | exact resolve eq27 eq10095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10099 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10095 eq65
    | (have r₁ := eq65
       have r₂ := eq10095
       grind)
    | exact resolve eq65 eq10095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq10101 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10095 eq261
    | exact resolve eq261 eq10095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq10095
  have eq10113 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10099
  have eq10169 : (τ (σ y)) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10101 eq128
    | exact resolve eq128 eq10101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10226 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq10169
    | exact resolve eq10169 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10169
  have eq10356 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10113 eq58
    | exact resolve eq58 eq10113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq10357 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10113 eq92
    | exact resolve eq92 eq10113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq10113
  have eq10370 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq10357
  have eq10381 : (k x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128 eq10356
    | exact resolve eq10356 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq10356
  have eq10384 : (k x y) = (M.op y y) := by
    first
    | (have r₁ := eq10381
       have r₂ := eq64
       grind)
    | exact resolve eq10381 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq10381
  have eq10390 : (k (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq10384
       grind)
    | exact superpose eq10384 eq44
    | exact resolve eq44 eq10384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10408 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10390
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq10390
    | exact resolve eq10390 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10390
  have eq21985 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10370 eq10101
    | exact resolve eq10101 eq10370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10101 eq10370
  have eq22065 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq21985
  have eq22071 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22065
       have r₂ := eq10097
       grind)
    | exact resolve eq22065 eq10097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10097 eq22065
  have eq22352 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq22071
       grind)
    | exact superpose eq22071 eq110
    | (have r₁ := eq110
       have r₂ := eq22071
       grind)
    | exact resolve eq110 eq22071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq22071
  have eq22411 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq22352
  have eq22412 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq22411
  have eq22424 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22412
       have i₂ := eq10384
       grind)
    | exact superpose eq10384 eq22412
    | exact resolve eq22412 eq10384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10384 eq22412
  have eq23381 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10226
       have i₂ := eq22424
       grind)
    | exact superpose eq22424 eq10226
    | exact resolve eq10226 eq22424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10226 eq22424
  have eq23461 : y = (M.op x y) := by grind
  clear eq23381
  have eq23483 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq23461 eq20
    | exact resolve eq20 eq23461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq23484 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23461 eq45
    | exact resolve eq45 eq23461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq23531 : y = (M.op y y) := by
    first
    | exact superpose eq23461 eq254
    | exact resolve eq254 eq23461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq23461
  have eq23602 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq23484
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq23484
    | exact resolve eq23484 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq23484
  have eq23603 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq23483
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23483
    | exact resolve eq23483 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23483
  have eq23627 : (k (σ x) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq10408 eq23602
    | exact resolve eq23602 eq10408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23602
  have eq23878 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23603 eq26
    | exact resolve eq26 eq23603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq24047 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq23531
       grind)
    | exact superpose eq23531 eq121
    | exact resolve eq121 eq23531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq23531
  have eq24158 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23603 eq24047
    | exact resolve eq24047 eq23603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24047
  have eq24173 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq24158
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24158
    | exact resolve eq24158 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq24158
  have eq24184 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23603 eq24173
    | exact resolve eq24173 eq23603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24173
  have eq24831 : (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23603 eq23627
    | exact resolve eq23627 eq23603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23627
  have eq24832 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq24184 eq24831
    | exact resolve eq24831 eq24184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24831
  have eq24843 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq24832 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq24832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24832
  have eq24855 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq24843
  have eq24859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23878 eq24855
    | exact resolve eq24855 eq23878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24855
  have eq24870 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq24859
       have r₂ := eq27
       grind)
    | exact resolve eq24859 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24859
  have eq24881 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23878 eq24870
    | exact resolve eq24870 eq23878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23878 eq24870
  have eq24953 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq24881 eq111
    | (have r₁ := eq111
       have r₂ := eq24881
       grind)
    | exact resolve eq111 eq24881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq24881
  have eq25016 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq24953
  have eq25024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq23603 eq25016
    | exact resolve eq25016 eq23603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25016
  have eq25025 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq25024
       have r₂ := eq27
       grind)
    | exact resolve eq25024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25024
  have eq25026 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq10408 eq25025
    | exact resolve eq25025 eq10408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10408 eq25025
  have eq25027 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23603 eq25026
    | exact resolve eq25026 eq23603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23603 eq25026
  have eq25028 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24184 eq25027
    | exact resolve eq25027 eq24184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24184 eq25027
  have eq25029 : False := by grind
  exact eq25029

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxy_x_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X0)
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq71 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq376 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq71
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq71 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq389 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq376 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq393 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq388 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq388 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq388 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq408 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq393 (σ X0)
       grind)
    | exact superpose eq393 eq15
    | exact resolve eq15 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq408 X0
       have i₂ := eq393 X0
       grind)
    | exact superpose eq393 eq408
    | exact resolve eq408 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq408
  have eq480 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq71 (σ X0) (σ X0)
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq71
    | exact resolve eq71 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq480 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq480
    | exact resolve eq480 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq487 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq482 X0
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq482
    | exact resolve eq482 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq482
  have eq529 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq389 (τ X1) X0
       grind)
    | exact superpose eq389 eq19
    | (have j1 := eq389 (τ X1) X0
       grind)
    | exact resolve eq19 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq532 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq389 (σ X1) (σ X0)
       grind)
    | exact superpose eq389 eq15
    | (have j1 := eq389 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq555 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq532
  have eq1075 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq529
    | exact resolve eq529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq1136 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1075 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1075
    | (have j0 := eq1075 X0 X1
       grind)
    | exact resolve eq1075 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1635 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq555 x y
       grind)
    | exact superpose eq555 eq16
    | (have j1 := eq555 x y
       grind)
    | exact resolve eq16 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq1708 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1635
       have i₂ := eq1136 y x
       grind)
    | exact superpose eq1136 eq1635
    | (have j1 := eq1136 y x
       grind)
    | (have r₁ := eq1635
       have r₂ := eq1136 y x
       grind)
    | exact resolve eq1635 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136 eq1635
  have eq1709 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1708
  have eq1717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq487 x
       have i₂ := eq1709
       grind)
    | exact superpose eq1709 eq487
    | exact resolve eq487 eq1709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709
  have eq1737 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1717
       have r₂ := eq16
       grind)
    | exact resolve eq1717 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1743 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1737
       grind)
    | exact superpose eq1737 eq10
    | exact resolve eq10 eq1737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq1790 : y = (M.op x x) := by
    first
    | (have i₁ := eq1743
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1743
    | exact resolve eq1743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq487 x
       have i₂ := eq1790
       grind)
    | exact superpose eq1790 eq487
    | exact resolve eq487 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq1790
  have eq1817 : False := by grind
  exact eq1817

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq74 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq91 y x
       grind)
    | exact superpose eq91 eq70
    | (have j1 := eq91 y x
       grind)
    | exact resolve eq70 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq91
    | (have j0 := eq91 (σ y) (σ x)
       grind)
    | exact resolve eq91 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq27
    | exact resolve eq27 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37
  have eq360 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq74
    | (have r₁ := eq74
       have r₂ := eq126
       grind)
    | exact resolve eq74 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq126
  have eq361 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq360
  have eq909 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq361 eq117
    | exact resolve eq117 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq913 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq909
  have eq918 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq913
       have r₂ := eq128
       grind)
    | exact resolve eq913 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq913
  have eq922 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq918 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq918
       grind)
    | exact resolve eq13 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq928 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq922 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq928 eq117
    | exact resolve eq117 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq928
  have eq940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq937
  have eq945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq940
    | exact resolve eq940 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq947 : y = (M.op x y) := by
    first
    | (have r₁ := eq945
       have r₂ := eq27
       grind)
    | exact resolve eq945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq949 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq947 eq20
    | exact resolve eq20 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq947 eq73
    | (have r₁ := eq73
       have r₂ := eq947
       grind)
    | exact resolve eq73 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq958 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq953
  have eq964 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq949
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq949
    | exact resolve eq949 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq966 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq964 eq26
    | exact resolve eq26 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1743 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq958
       grind)
    | exact superpose eq958 eq70
    | exact resolve eq70 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq958
  have eq1750 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq964 eq1743
    | exact resolve eq1743 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1752 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1750
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1750
    | exact resolve eq1750 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1750
  have eq1753 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq964 eq1752
    | exact resolve eq1752 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq1752
  have eq1759 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1753 eq91
    | (have j0 := eq91 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq91 eq1753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1760 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq1759
  have eq1762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq966 eq1760
    | exact resolve eq1760 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760
  have eq1765 : x = (M.op x x) := by
    first
    | (have r₁ := eq1762
       have r₂ := eq27
       grind)
    | exact resolve eq1762 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq1770 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1765
       grind)
    | exact superpose eq1765 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1765
       grind)
    | exact resolve eq13 eq1765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765
  have eq1776 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1770 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq1882 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq1776 sF0
       grind)
    | exact superpose eq1776 eq136
    | exact resolve eq136 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq1776
  have eq1888 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq947 eq1882
    | exact resolve eq1882 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947 eq1882
  have eq1891 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1888
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1888
    | exact resolve eq1888 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1888
  have eq1894 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq1891
    | exact resolve eq1891 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1891
  have eq1909 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1894 eq91
    | (have j0 := eq91 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq91 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1894
  have eq1910 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1909
  have eq1912 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq966 eq1910
    | exact resolve eq1910 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq1910
  have eq1915 : False := by grind
  exact eq1915

/-- `Equation4425`: `x ◇ (x ◇ y) = (z ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxx_x_pxy_Equation4425 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4425 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4425.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X2) := by
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
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X3 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ (M.op x x)) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq35 (M.op x x)
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq35
    | exact resolve eq35 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq181 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq178 sF0
       grind)
    | exact superpose eq178 eq37
    | exact resolve eq37 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq178 sF2
       grind)
    | exact superpose eq178 eq90
    | exact resolve eq90 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq560 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 X2 X3 X4 (M.op X4 x)
       have i₂ := eq177 X4 x X0 X1
       grind)
    | (have i₁ := eq177 X2 X3 X4 (M.op X4 x)
       have i₂ := eq177 X0 X1 X4 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 X1 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X4) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq177 X2 x X0 X1
       grind)
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq177 X0 X1 X2 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq565 x x
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq565 (σ x) (σ y)
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq565
    | (have j0 := eq565 (σ x) (σ y)
       have j1 := eq566 x y
       grind)
    | exact resolve eq565 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq579 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq560 x x X2 X3 X4
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq560 (σ x) (σ y) X2 X3 X4
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq560
    | (have j0 := eq560 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq560 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq589 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq579 x x X4
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq579 (σ x) (σ y) X4
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq579
    | (have j0 := eq579 (σ x) (σ y) X4
       grind)
    | exact resolve eq579 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq612 : ∀ X2 : G, (M.op (M.op X2 X2) X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | (have i₁ := eq16 x x X2
       have i₂ := eq566 x x
       grind)
    | (have i₁ := eq16 (σ x) (σ y) X2
       have i₂ := eq566 x x
       grind)
    | exact superpose eq566 eq16
    | (have j0 := eq16 (σ x) (σ y) X2
       grind)
    | exact resolve eq16 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq589 eq178
    | exact resolve eq178 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq898 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq900 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq944 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1025 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq898
       grind)
    | exact superpose eq898 eq40
    | exact resolve eq40 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1026 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1025
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1025
    | exact resolve eq1025 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1025
  have eq1028 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1026
    | exact resolve eq1026 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1028 eq900
    | exact resolve eq900 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1350 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1343
       have r₂ := eq27
       grind)
    | exact resolve eq1343 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq1355 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1350 eq182
    | exact resolve eq182 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1350
  have eq1386 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq1355
    | exact resolve eq1355 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq1391 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq898 eq1386
    | exact resolve eq1386 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq1386
  have eq1392 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1391
  have eq1395 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq179
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq179
    | exact resolve eq179 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1400 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq566 x x
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq566
    | exact resolve eq566 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1401 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq573 x x X1 X0
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq573
    | exact resolve eq573 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq1392
  have eq1421 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1401 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1401
    | (have j0 := eq1401 X0 X1
       grind)
    | exact resolve eq1401 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1422 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1400
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1400
    | exact resolve eq1400 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1426 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1395
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1395
    | exact resolve eq1395 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq1428 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq1421 x X1
       have i₂ := eq612 x
       grind)
    | exact superpose eq612 eq1421
    | exact resolve eq1421 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq1421
  have eq1431 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq1422 eq1428
    | exact resolve eq1428 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1469 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1426 eq900
    | exact resolve eq900 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq1426
  have eq1473 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1469
  have eq1512 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1431 eq181
    | exact resolve eq181 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq1431
  have eq1514 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1512
    | exact resolve eq1512 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1581 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1473 eq566
    | exact resolve eq566 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1586 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1581
    | exact resolve eq1581 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1598 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1422 eq1586
    | exact resolve eq1586 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1614 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1598 eq589
    | exact resolve eq589 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1615 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1598 eq635
    | exact resolve eq635 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1617 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq1620 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1615
    | exact resolve eq1615 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615
  have eq1621 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1614
    | (have j0 := eq1614 X0
       grind)
    | exact resolve eq1614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq1623 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1598 eq1620
    | exact resolve eq1620 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620
  have eq1624 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1598 eq1621
    | exact resolve eq1621 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621
  have eq1629 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1514 eq945
    | (have j0 := eq945 (σ (M.op x y))
       grind)
    | (have r₁ := eq945 (σ (M.op x y))
       have r₂ := eq1514
       grind)
    | exact resolve eq945 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq1514
  have eq1630 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1629
  have eq1665 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1630 eq566
    | exact resolve eq566 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1669 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1422 eq1665
    | exact resolve eq1665 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq1665
  have eq1693 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1623 eq152
    | exact resolve eq152 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1696 : y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1693
    | exact resolve eq1693 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq1792 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1669 eq1630
    | exact resolve eq1630 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630 eq1669
  have eq1812 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq1792
  have eq1839 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1812 eq589
    | exact resolve eq589 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq1840 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1812 eq635
    | exact resolve eq635 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1843 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1840
    | exact resolve eq1840 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq1844 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1839
    | (have j0 := eq1839 X0
       grind)
    | exact resolve eq1839 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839
  have eq1846 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1812 eq1843
    | exact resolve eq1843 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq1847 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1812 eq1844
    | exact resolve eq1844 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq2267 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq943 y y
       have i₂ := eq1696
       grind)
    | exact superpose eq1696 eq943
    | (have j0 := eq943 y y
       grind)
    | (have r₁ := eq943 y y
       have r₂ := eq1696
       grind)
    | exact resolve eq943 eq1696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq2268 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2267
  have eq2269 : y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2268
  have eq2282 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1846 eq152
    | exact resolve eq152 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1846
  have eq2288 : y = (k y y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq2282
    | exact resolve eq2282 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2282
  have eq2405 : (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq566 y y
       have i₂ := eq2269
       grind)
    | exact superpose eq2269 eq566
    | exact resolve eq566 eq2269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2409 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2269 eq2405
    | exact resolve eq2405 eq2269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269 eq2405
  have eq2422 : y = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1598 eq2409
    | exact resolve eq2409 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2434 : y = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2422
    | exact resolve eq2422 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422
  have eq2446 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1598 eq2434
    | exact resolve eq2434 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598 eq2434
  have eq2472 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2446 eq27
    | exact resolve eq27 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446
  have eq2538 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq943 y y
       have i₂ := eq2288
       grind)
    | exact superpose eq2288 eq943
    | (have j0 := eq943 y y
       grind)
    | (have r₁ := eq943 y y
       have r₂ := eq2288
       grind)
    | exact resolve eq943 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2288
  have eq2539 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2538
  have eq2540 : y = (M.op y y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2539
  have eq2561 : (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq566 y y
       have i₂ := eq2540
       grind)
    | exact superpose eq2540 eq566
    | exact resolve eq566 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2565 : (M.op (σ x) (σ y)) = (M.op y y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1812 eq2561
    | exact resolve eq2561 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2578 : (M.op (σ x) (σ y)) = (M.op y y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2565
    | exact resolve eq2565 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq2590 : (σ y) = (M.op y y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1812 eq2578
    | exact resolve eq2578 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812 eq2578
  have eq2725 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2540
       have i₂ := eq2590
       grind)
    | exact superpose eq2590 eq2540
    | exact resolve eq2540 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540 eq2590
  have eq2749 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2725
  have eq2767 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2749
       have r₂ := eq2472
       grind)
    | exact resolve eq2749 eq2472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472 eq2749
  have eq2808 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2767
       grind)
    | exact superpose eq2767 eq18
    | exact resolve eq18 eq2767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2822 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq2767
  have eq2854 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2808 eq1847
    | exact resolve eq1847 eq2808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq2855 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2808 eq1624
    | exact resolve eq1624 eq2808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624 eq2808
  have eq2863 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2855
  have eq2864 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2854
  have eq2872 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2863
       have r₂ := eq1617
       grind)
    | exact resolve eq2863 eq1617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617 eq2863
  have eq2873 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2864
       have r₂ := eq2822
       grind)
    | exact resolve eq2864 eq2822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822 eq2864
  have eq2880 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2872 eq27
    | exact resolve eq27 eq2872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq2892 : y = (M.op x y) := by
    first
    | (have r₁ := eq2880
       have r₂ := eq2873
       grind)
    | exact resolve eq2880 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873 eq2880
  have eq2894 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2892
       grind)
    | exact superpose eq2892 eq18
    | exact resolve eq18 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2895 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2892
       grind)
    | exact superpose eq2892 eq24
    | exact resolve eq24 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2892
  have eq2903 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2895 eq20
    | exact resolve eq20 eq2895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895
  have eq2973 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2894 eq574
    | exact resolve eq574 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq2894
  have eq2992 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2973 eq635
    | exact resolve eq635 eq2973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq2999 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq2973 eq177
    | exact resolve eq177 eq2973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3000 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq2973 eq566
    | exact resolve eq566 eq2973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq2973
  have eq3003 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3000 eq2999
    | exact resolve eq2999 eq3000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999
  have eq3010 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2992 eq37
    | exact resolve eq37 eq2992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2992
  have eq3018 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3010
    | exact resolve eq3010 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3010
  have eq3020 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq2903 eq3018
    | exact resolve eq3018 eq2903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018
  have eq3166 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3020 eq943
    | (have j0 := eq943 (σ y) (σ y)
       grind)
    | (have r₁ := eq943 (σ y) (σ y)
       have r₂ := eq3020
       grind)
    | exact resolve eq943 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq3020
  have eq3167 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3166
  have eq3168 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3167
  have eq3194 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq3168 eq177
    | exact resolve eq177 eq3168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq3200 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq3168 eq3194
    | exact resolve eq3194 eq3168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168 eq3194
  have eq3212 : (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq3200 x x
       have i₂ := eq3003 x x
       grind)
    | exact superpose eq3003 eq3200
    | exact resolve eq3200 eq3003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003 eq3200
  have eq3223 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq3212 eq26
    | exact resolve eq26 eq3212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3266 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3000 eq3223
    | exact resolve eq3223 eq3000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3000 eq3223
  have eq3349 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq3266 eq27
    | exact resolve eq27 eq3266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3266
  have eq3361 : (M.op x y) ≠ (σ y) := by
    first
    | exact superpose eq2903 eq3349
    | exact resolve eq3349 eq2903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2903 eq3349
  have eq3363 : False := by grind
  exact eq3363
