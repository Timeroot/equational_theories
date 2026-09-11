import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq45
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq96 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq106 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq99 (σ X0)
       grind)
    | exact superpose eq99 eq32
    | exact resolve eq32 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq107 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq99 (τ X0)
       grind)
    | exact superpose eq99 eq36
    | exact resolve eq36 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq108 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq99 (τ X0)
       grind)
    | exact superpose eq99 eq18
    | exact resolve eq18 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq109 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq108
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq107
    | exact resolve eq107 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq111 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq106
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq109
    | exact resolve eq109 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq118 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq111
    | exact resolve eq111 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq111
  have eq121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq117 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq117
    | exact resolve eq117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq138 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq294 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 (σ X0) X1 (σ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq26
    | exact resolve eq26 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq35
    | exact resolve eq35 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq110
  have eq305 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq304 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq304
    | exact resolve eq304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq306 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    grind
  clear eq305
  have eq312 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq306 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq306
    | exact resolve eq306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq338 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq312 X0
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq312
    | exact resolve eq312 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq312
  have eq345 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq338
    | exact resolve eq338 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq522 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq138
       have i₂ := eq121 y
       grind)
    | exact superpose eq121 eq138
    | exact resolve eq138 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq523 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq522
       have i₂ := eq121 x
       grind)
    | exact superpose eq121 eq522
    | exact resolve eq522 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq524 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq523
       have i₂ := eq121 y
       grind)
    | exact superpose eq121 eq523
    | exact resolve eq523 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq525 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq524
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq524
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq524 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq526 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq525
  have eq8775 : (M.op y y) = (τ (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq526
       grind)
    | exact superpose eq526 eq10
    | exact resolve eq10 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq8816 : x = (M.op y y) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq8775
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8775
    | exact resolve eq8775 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8775
  have eq8817 : x = (M.op y y) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq8816
  have eq96880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq345 y
       have i₂ := eq8817
       grind)
    | exact superpose eq8817 eq345
    | exact resolve eq345 eq8817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq8817
  have eq96968 : (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq96880
       have r₂ := eq16
       grind)
    | exact resolve eq96880 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96880
  have eq97450 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq294 y X0 X1
       have i₂ := eq96968
       grind)
    | exact superpose eq96968 eq294
    | exact resolve eq294 eq96968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97532 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 y X0 y
       have i₂ := eq96968
       grind)
    | exact superpose eq96968 eq26
    | exact resolve eq26 eq96968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96968
  have eq97540 : ∀ X0 : G, (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq97532 X0 x
       have i₂ := eq26 x x X0 x
       grind)
    | exact superpose eq26 eq97532
    | exact resolve eq97532 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97532
  have eq97554 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq97450 X0 x
       have i₂ := eq294 x X0 x
       grind)
    | exact superpose eq294 eq97450
    | exact resolve eq97450 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97450
  have eq97983 : ∀ X0 : G, (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq97540 X0
       grind)
    | exact superpose eq97540 eq10
    | (have j1 := eq97540 X0
       grind)
    | exact resolve eq10 eq97540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97540
  have eq98202 : ∀ X0 : G, (M.op y y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq97983 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq97983
    | (have j0 := eq97983 X0
       grind)
    | exact resolve eq97983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97983
  have eq98818 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X1 y X0 y
       have i₂ := eq98202 X2
       grind)
    | exact superpose eq98202 eq26
    | (have j1 := eq98202 X2
       grind)
    | exact resolve eq26 eq98202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98202
  have eq98827 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X2
    first
    | (have i₁ := eq98818 X0 x X2
       have i₂ := eq26 x x X0 x
       grind)
    | exact superpose eq26 eq98818
    | (have j0 := eq98818 X0 x X0
       grind)
    | exact resolve eq98818 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq98818
  have eq100013 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq98827 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98827
  have eq100014 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq100013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100013
  have eq100450 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq294 y X0 X1
       have i₂ := eq100014 y
       grind)
    | exact superpose eq100014 eq294
    | exact resolve eq294 eq100014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176341 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq97554 X0
       have i₂ := eq100014 y
       grind)
    | exact superpose eq100014 eq97554
    | (have j0 := eq97554 X0
       grind)
    | exact resolve eq97554 eq100014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97554
  have eq177199 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) ∨ (M.op X2 (σ y)) = (M.op X2 (σ x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100450 X0 X1
       have i₂ := eq176341 X2
       grind)
    | exact superpose eq176341 eq100450
    | (have j1 := eq176341 X2
       grind)
    | exact resolve eq100450 eq176341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100450 eq176341
  have eq177524 : ∀ X0 X2 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X2 (σ y)) = (M.op X2 (σ x)) := by
    intro X0 X2
    first
    | (have i₁ := eq177199 X0 x X2
       have i₂ := eq294 x X0 x
       grind)
    | exact superpose eq294 eq177199
    | (have j0 := eq177199 X0 x X0
       grind)
    | exact resolve eq177199 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq177199
  have eq199090 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq177524 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177524
  have eq199091 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq199090 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199090
  have eq200058 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199091 (σ x)
       grind)
    | exact superpose eq199091 eq16
    | exact resolve eq16 eq199091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199091
  have eq200225 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq200058
       have i₂ := eq121 x
       grind)
    | exact superpose eq121 eq200058
    | exact resolve eq200058 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq200058
  have eq200508 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq200225
       have i₂ := eq100014 x
       grind)
    | exact superpose eq100014 eq200225
    | exact resolve eq200225 eq100014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100014 eq200225
  have eq200509 : False := by grind
  exact eq200509

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq376 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq6060 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq376 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq376 X0 X1
       grind)
    | exact superpose eq376 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq376 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq376 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq376 X0 X1
       grind)
    | exact resolve eq13 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6062 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X0)) = (M.op X2 (M.op (M.op (σ X0) (σ X1)) X3)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X3 (σ X0) X2 (σ X1)
       have i₂ := eq376 X0 X1
       grind)
    | (have i₁ := eq64 X0 (σ X1) X2 (σ X0)
       have i₂ := eq376 X0 X1
       grind)
    | exact superpose eq376 eq64
    | (have j1 := eq376 X0 X1
       grind)
    | exact resolve eq64 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq6064 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6060 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6060
  have eq6065 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6064 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6064
  have eq6069 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6062 X0 X1 X2 x
       have i₂ := eq64 x (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq64 eq6062
    | (have j0 := eq6062 X0 X1 X2 x
       grind)
    | exact resolve eq6062 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq6062
  have eq6071 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6065 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6065
    | (have j0 := eq6065 X0 X1
       grind)
    | exact resolve eq6065 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6065
  have eq9074 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6069 (τ X0) (τ X1) X2
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq6069
    | (have j0 := eq6069 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq6069 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6069
  have eq9231 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9074 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9074
    | (have j0 := eq9074 X0 X1 X2
       grind)
    | exact resolve eq9074 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9074
  have eq9272 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9231 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9231
    | (have j0 := eq9231 X0 X1 X2
       grind)
    | exact resolve eq9231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9231
  have eq9313 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9272 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9272
    | (have j0 := eq9272 X0 X1 X2
       grind)
    | exact resolve eq9272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9272
  have eq9342 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (σ (τ X0))) ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9313 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9313
    | (have j0 := eq9313 X0 X1 X2
       grind)
    | exact resolve eq9313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9313
  have eq9371 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9342 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9342
    | (have j0 := eq9342 X0 X1 X2
       grind)
    | exact resolve eq9342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9342
  have eq9400 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9371 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9371
    | (have j0 := eq9371 X0 X1 X2
       grind)
    | exact resolve eq9371 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9371
  have eq9413 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9400 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9400
    | (have j0 := eq9400 X0 X1 X2
       grind)
    | exact resolve eq9400 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9400
  have eq10987 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6071 (τ X1) (τ X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq6071
    | (have j0 := eq6071 (τ X0) (τ X1)
       grind)
    | exact resolve eq6071 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6071
  have eq11158 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10987 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq10987
    | (have j0 := eq10987 X0 X1
       grind)
    | exact resolve eq10987 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10987
  have eq11199 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11158 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11158
    | (have j0 := eq11158 X0 X1
       grind)
    | exact resolve eq11158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11158
  have eq11237 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11199 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11199
    | (have j0 := eq11199 X0 X1
       grind)
    | exact resolve eq11199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11199
  have eq11269 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11237 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11237
    | (have j0 := eq11237 X0 X1
       grind)
    | exact resolve eq11237 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11237
  have eq11294 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11269 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11269
    | (have j0 := eq11269 X0 X1
       grind)
    | exact resolve eq11269 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11269
  have eq11315 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11294 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11294
    | (have j0 := eq11294 X0 X1
       grind)
    | exact resolve eq11294 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11294
  have eq11332 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11315 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11315
    | (have j0 := eq11315 X0 X1
       grind)
    | exact resolve eq11315 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11315
  have eq11635 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11332 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11332
  have eq11640 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11635 X0 X1
       have j1 := eq9413 X0 X1 x
       grind)
    | (have r₁ := eq11635 X0 X1
       have r₂ := eq9413 X0 X1 X0
       grind)
    | (have r₁ := eq11635 X1 X0
       have r₂ := eq9413 X0 X1 X1
       grind)
    | (have r₁ := eq11635 X1 X1
       have r₂ := eq9413 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq11635 eq9413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9413 eq11635
  have eq11680 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11640 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11640
    | (have j0 := eq11640 (σ X0) (σ X1)
       grind)
    | exact resolve eq11640 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12535 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11680 X0 X1
       have i₂ := eq11640 X0 X1
       grind)
    | exact superpose eq11640 eq11680
    | (have j0 := eq11680 X0 X1
       have j1 := eq11640 (σ X0) (σ X1)
       grind)
    | exact resolve eq11680 eq11640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16356 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12535 x y
       grind)
    | exact superpose eq12535 eq16
    | (have j1 := eq12535 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq12535 x y
       grind)
    | exact resolve eq16 eq12535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12535
  have eq16385 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq16356
  have eq16460 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq16385
  have eq16488 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16460
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16460
    | exact resolve eq16460 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16460
  have eq16503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq11640 eq16488
    | (have j1 := eq11640 x y
       grind)
    | exact resolve eq16488 eq11640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11640 eq16488
  have eq16511 : x = (M.op y y) := by
    first
    | (have r₁ := eq16503
       have r₂ := eq16
       grind)
    | exact resolve eq16503 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16503
  have eq16514 : (M.op x y) = (k x y) := by grind
  clear eq16511
  have eq16537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11680 x y
       have i₂ := eq16514
       grind)
    | exact superpose eq16514 eq11680
    | (have j0 := eq11680 x y
       grind)
    | exact resolve eq11680 eq16514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11680
  have eq16538 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq16537
       have r₂ := eq16
       grind)
    | exact resolve eq16537 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16537
  have eq16575 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq16538
  have eq16603 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16575
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq16575
    | exact resolve eq16575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16575
  have eq16617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16603
       have i₂ := eq16514
       grind)
    | exact superpose eq16514 eq16603
    | exact resolve eq16603 eq16514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16514 eq16603
  have eq16626 : False := by grind
  exact eq16626

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq86 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq208 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq86 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq213 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq208 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq214 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq220 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq214
    | (have j0 := eq214 X0 X1
       grind)
    | exact resolve eq214 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq221 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq220 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq568 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq221 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq221
    | exact resolve eq221 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq221 x y
       grind)
    | exact superpose eq221 eq16
    | (have j1 := eq221 x y
       grind)
    | exact resolve eq16 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq591 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq568
    | (have j0 := eq568 X0 X1
       grind)
    | exact resolve eq568 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq568
  have eq593 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq591
    | exact resolve eq591 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq652 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq593 (τ X0) X1
       grind)
    | exact superpose eq593 eq18
    | (have j1 := eq593 (τ X0) X1
       grind)
    | exact resolve eq18 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq593
  have eq899 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq652 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq652
    | exact resolve eq652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq954 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq899 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq899
    | (have j0 := eq899 X0 X1
       grind)
    | exact resolve eq899 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq1054 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq576
       have i₂ := eq954 x y
       grind)
    | exact superpose eq954 eq576
    | (have j1 := eq954 (σ x) (σ y)
       grind)
    | (have r₁ := eq576
       have r₂ := eq954 x y
       grind)
    | exact resolve eq576 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1054
  have eq1058 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1055
  have eq1097 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq576
       have i₂ := eq1058
       grind)
    | exact superpose eq1058 eq576
    | exact resolve eq576 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq1058
  have eq1098 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1097
  have eq1099 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1098
  have eq1106 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1099
  have eq1118 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1106
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1106
    | exact resolve eq1106 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1151 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1118
       grind)
    | exact superpose eq1118 eq16
    | exact resolve eq16 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1163 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1151
       have i₂ := eq954 x y
       grind)
    | exact superpose eq954 eq1151
    | (have j1 := eq954 x y
       grind)
    | (have r₁ := eq1151
       have r₂ := eq954 x y
       grind)
    | exact resolve eq1151 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1164 : x = (M.op y y) := by grind
  clear eq1163
  have eq1191 : (M.op x y) = (k x y) := by grind
  clear eq1164
  have eq1203 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1151
       have i₂ := eq1191
       grind)
    | exact superpose eq1191 eq1151
    | exact resolve eq1151 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq1191
  have eq1206 : False := by grind
  exact eq1206

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq376 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq4099 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq376 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq376 X0 X1
       grind)
    | exact superpose eq376 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq376 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq376 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq376 X0 X1
       grind)
    | exact resolve eq13 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4101 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X0)) = (M.op X2 (M.op (M.op (σ X0) (σ X1)) X3)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X3 (σ X0) X2 (σ X1)
       have i₂ := eq376 X0 X1
       grind)
    | (have i₁ := eq64 X0 (σ X1) X2 (σ X0)
       have i₂ := eq376 X0 X1
       grind)
    | exact superpose eq376 eq64
    | (have j1 := eq376 X0 X1
       grind)
    | exact resolve eq64 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4103 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4099 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4099
  have eq4104 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4103
  have eq4108 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4101 X0 X1 X2 x
       have i₂ := eq64 x (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq64 eq4101
    | (have j0 := eq4101 X0 X1 X2 x
       grind)
    | exact resolve eq4101 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq4101
  have eq4110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4104 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4104
    | (have j0 := eq4104 X0 X1
       grind)
    | exact resolve eq4104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104
  have eq11179 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4110
  have eq50917 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11179 X0 X1
       have i₂ := eq376 X0 X1
       grind)
    | (have i₁ := eq11179 X1 X0
       have i₂ := eq376 X0 X1
       grind)
    | exact superpose eq376 eq11179
    | (have j0 := eq11179 X1 X0
       have j1 := eq376 X1 X0
       grind)
    | (have r₁ := eq11179 X0 X0
       have r₂ := eq376 X0 X0
       grind)
    | (have r₁ := eq11179 X1 X1
       have r₂ := eq376 X1 X1
       grind)
    | exact resolve eq11179 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq11179
  have eq50988 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq50917 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50917
  have eq50999 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq50988 X0 X1
       have j1 := eq4108 X1 X0 x
       grind)
    | (have r₁ := eq50988 X0 X1
       have r₂ := eq4108 X0 X1 (σ X0)
       grind)
    | (have r₁ := eq50988 X1 X0
       have r₂ := eq4108 X0 X1 (σ X1)
       grind)
    | exact resolve eq50988 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108 eq50988
  have eq51048 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50999 (τ X0) (τ X1)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq50999
    | (have j0 := eq50999 (τ X1) (τ X0)
       grind)
    | exact resolve eq50999 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq50999
  have eq51336 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51048 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq51048
    | (have j0 := eq51048 X0 X1
       grind)
    | exact resolve eq51048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51048
  have eq51406 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51336 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51336
    | (have j0 := eq51336 X0 X1
       grind)
    | exact resolve eq51336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51336
  have eq51475 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51406 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq51406
    | (have j0 := eq51406 X0 X1
       grind)
    | exact resolve eq51406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51406
  have eq51537 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51475 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51475
    | (have j0 := eq51475 X0 X1
       grind)
    | exact resolve eq51475 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51475
  have eq51591 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51537 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq51537
    | (have j0 := eq51537 X0 X1
       grind)
    | exact resolve eq51537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51537
  have eq51640 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51591 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq51591
    | (have j0 := eq51591 X0 X1
       grind)
    | exact resolve eq51591 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51591
  have eq51673 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51640 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51640
    | (have j0 := eq51640 X0 X1
       grind)
    | exact resolve eq51640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51640
  have eq51694 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51673 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51673
    | (have j0 := eq51673 X0 X1
       grind)
    | exact resolve eq51673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51673
  have eq52076 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51694 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51694
  have eq52092 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52076 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq52076 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq52076 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq52076 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq52076 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52076
  have eq52159 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52092 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52092
    | (have j0 := eq52092 (σ X0) (σ X1)
       grind)
    | exact resolve eq52092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53252 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52159 X0 X1
       have i₂ := eq52092 X0 X1
       grind)
    | exact superpose eq52092 eq52159
    | (have j0 := eq52159 X0 X1
       have j1 := eq52092 (σ X0) (σ X1)
       grind)
    | exact resolve eq52159 eq52092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57454 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53252 x y
       grind)
    | exact superpose eq53252 eq16
    | (have j1 := eq53252 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq53252 x y
       grind)
    | exact resolve eq16 eq53252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53252
  have eq57486 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq57454
  have eq57641 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq57486
  have eq57670 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq57641
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq57641
    | exact resolve eq57641 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57641
  have eq57701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq52092 eq57670
    | (have j1 := eq52092 x y
       grind)
    | exact resolve eq57670 eq52092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52092 eq57670
  have eq57725 : x = (M.op y y) := by
    first
    | (have r₁ := eq57701
       have r₂ := eq16
       grind)
    | exact resolve eq57701 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57701
  have eq57728 : (M.op x y) = (k x y) := by grind
  clear eq57725
  have eq57751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq52159 x y
       have i₂ := eq57728
       grind)
    | exact superpose eq57728 eq52159
    | (have j0 := eq52159 x y
       grind)
    | exact resolve eq52159 eq57728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52159
  have eq57753 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq57751
       have r₂ := eq16
       grind)
    | exact resolve eq57751 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57751
  have eq57811 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq57753
  have eq57840 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq57811
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq57811
    | exact resolve eq57811 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57811
  have eq57870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57840
       have i₂ := eq57728
       grind)
    | exact superpose eq57728 eq57840
    | exact resolve eq57840 eq57728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57728 eq57840
  have eq57895 : False := by grind
  exact eq57895

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq205 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq89 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq89 X0 X0
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq217 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq218 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq217 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq220 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq218
    | (have j0 := eq218 X0 X1
       grind)
    | exact resolve eq218 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq223 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq220 X0 X1
       have j1 := eq214 X1 X0
       grind)
    | (have r₁ := eq220 X1 X0
       have r₂ := eq214 X0 X1
       grind)
    | (have r₁ := eq220 X1 (k X0 X1)
       have r₂ := eq214 X0 X1
       grind)
    | (have r₁ := eq220 X1 X1
       have r₂ := eq214 X1 X1
       grind)
    | exact resolve eq220 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq220
  have eq562 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq223 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq223
    | exact resolve eq223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq223 y x
       grind)
    | exact superpose eq223 eq16
    | (have j1 := eq223 y x
       grind)
    | exact resolve eq16 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq584 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq562
    | (have j0 := eq562 X0 X1
       grind)
    | exact resolve eq562 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq562
  have eq586 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq584
    | exact resolve eq584 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq645 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq586 (τ X0) X1
       grind)
    | exact superpose eq586 eq18
    | (have j1 := eq586 (τ X0) X1
       grind)
    | exact resolve eq18 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq586
  have eq865 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq645 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq645
    | exact resolve eq645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq916 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq865 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq865
    | (have j0 := eq865 X0 X1
       grind)
    | exact resolve eq865 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq1019 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq570
       have i₂ := eq916 x y
       grind)
    | exact superpose eq916 eq570
    | (have j1 := eq916 (σ x) (σ y)
       grind)
    | (have r₁ := eq570
       have r₂ := eq916 x y
       grind)
    | exact resolve eq570 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1019
  have eq1024 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1020
  have eq1073 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq570
       have i₂ := eq1024
       grind)
    | exact superpose eq1024 eq570
    | exact resolve eq570 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq1024
  have eq1074 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1073
  have eq1075 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1074
  have eq1086 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1075
  have eq1095 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1086
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1086
    | exact resolve eq1086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1151 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1095
       grind)
    | exact superpose eq1095 eq16
    | exact resolve eq16 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1151
       have i₂ := eq916 x y
       grind)
    | exact superpose eq916 eq1151
    | (have j1 := eq916 x y
       grind)
    | (have r₁ := eq1151
       have r₂ := eq916 x y
       grind)
    | exact resolve eq1151 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq1163 : x = (M.op y y) := by grind
  clear eq1162
  have eq1198 : (M.op x y) = (k x y) := by grind
  clear eq1163
  have eq1207 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1151
       have i₂ := eq1198
       grind)
    | exact superpose eq1198 eq1151
    | exact resolve eq1151 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq1198
  have eq1210 : False := by grind
  exact eq1210

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq40 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq205 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq212 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq825 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq212 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq212
    | (have j0 := eq212 (τ X0) (τ X1)
       grind)
    | exact resolve eq212 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq825
    | (have j0 := eq825 X0 X1
       grind)
    | exact resolve eq825 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq843 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq838 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq838
    | (have j0 := eq838 X0 X1
       grind)
    | exact resolve eq838 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq847 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq843
    | (have j0 := eq843 X0 X1
       grind)
    | exact resolve eq843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq850 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq847 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq847
    | (have j0 := eq847 X0 X1
       grind)
    | exact resolve eq847 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq853 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq850 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq850
    | (have j0 := eq850 X0 X1
       grind)
    | exact resolve eq850 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq854 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq853 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq853
    | (have j0 := eq853 X0 X1
       grind)
    | exact resolve eq853 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq2988 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq87 X1 X0
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq87 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq87 X0 (σ X0)
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3002 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq87 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq3003 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3002 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002
  have eq3004 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2988 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988
  have eq3005 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3004 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004
  have eq3007 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3003 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3003
    | (have j0 := eq3003 X0
       grind)
    | exact resolve eq3003 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq3043 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq3007 X0
       grind)
    | exact superpose eq3007 eq40
    | (have j1 := eq3007 X0
       grind)
    | exact resolve eq40 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3007
  have eq3058 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3043 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3043
    | (have j0 := eq3043 X0
       grind)
    | exact resolve eq3043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3043
  have eq3059 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3058 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3058
  have eq3061 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3059 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3059
    | exact resolve eq3059 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3084 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3059 X0
       grind)
    | exact superpose eq3059 eq11
    | exact resolve eq11 eq3059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3126 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3061 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq3061
    | exact resolve eq3061 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061
  have eq3354 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3126 X0
       grind)
    | exact superpose eq3126 eq11
    | exact resolve eq11 eq3126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3427 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3354 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3354
    | exact resolve eq3354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq3486 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq3427 (τ X0)
       grind)
    | exact superpose eq3427 eq36
    | exact resolve eq36 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3534 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3486 X0
       have i₂ := eq3126 X0
       grind)
    | exact superpose eq3126 eq3486
    | exact resolve eq3486 eq3126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3126 eq3486
  have eq4042 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4060 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4042 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4042
    | exact resolve eq4042 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4042
  have eq4092 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4060 X0
       have i₂ := eq3427 X0
       grind)
    | exact superpose eq3427 eq4060
    | exact resolve eq4060 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060
  have eq4109 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq4092
  have eq125959 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3005 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3005
    | exact resolve eq3005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126074 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) X0
       have i₂ := eq3005 (σ X0) X1
       grind)
    | exact superpose eq3005 eq26
    | (have j1 := eq3005 (σ X0) X1
       grind)
    | exact resolve eq26 eq3005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005
  have eq126197 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq126074 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq126074
    | (have j0 := eq126074 X0 X1
       grind)
    | exact resolve eq126074 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126074
  have eq126259 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125959 X0 X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq125959
    | (have j0 := eq125959 X0 X1
       grind)
    | exact resolve eq125959 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125959
  have eq126303 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq126197 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126197
    | (have j0 := eq126197 X0 X1
       grind)
    | exact resolve eq126197 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126197
  have eq126389 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq126303 X0 X1
       have i₂ := eq3084 X0
       grind)
    | exact superpose eq3084 eq126303
    | (have j0 := eq126303 X0 X1
       grind)
    | exact resolve eq126303 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126303
  have eq126444 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq126389 X0 X1
       have i₂ := eq3427 X0
       grind)
    | exact superpose eq3427 eq126389
    | (have j0 := eq126389 X0 X1
       grind)
    | exact resolve eq126389 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126389
  have eq126488 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq126444 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126444
    | (have j0 := eq126444 X0 X1
       grind)
    | exact resolve eq126444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126444
  have eq127639 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq126259 X0 X1
       grind)
    | exact superpose eq126259 eq11
    | (have j1 := eq126259 X0 X1
       grind)
    | exact resolve eq11 eq126259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126259
  have eq127862 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq127639 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq127639
    | (have j0 := eq127639 X0 X1
       grind)
    | exact resolve eq127639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127639
  have eq128204 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq127862 (τ X0) X1
       grind)
    | exact superpose eq127862 eq18
    | (have j1 := eq127862 (τ X0) X1
       grind)
    | exact resolve eq18 eq127862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq127862
  have eq134807 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq126488 (τ X0) (τ X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq126488
    | (have j0 := eq126488 (τ X1) (τ X0)
       grind)
    | exact resolve eq126488 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq126488
  have eq135245 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq134807 X0 X1
       have i₂ := eq3534 X1
       grind)
    | exact superpose eq3534 eq134807
    | (have j0 := eq134807 X0 X1
       grind)
    | exact resolve eq134807 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134807
  have eq135436 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq135245 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq135245
    | (have j0 := eq135245 X0 X1
       grind)
    | exact resolve eq135245 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135245
  have eq135592 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq135436 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq135436
    | (have j0 := eq135436 X0 X1
       grind)
    | exact resolve eq135436 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135436
  have eq135719 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135592 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq135592
    | (have j0 := eq135592 X0 X1
       grind)
    | exact resolve eq135592 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135592
  have eq135812 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135719 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq135719
    | (have j0 := eq135719 X0 X1
       grind)
    | exact resolve eq135719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135719
  have eq136246 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq135812 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135812
  have eq144114 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq128204 X1 (τ X0)
       grind)
    | exact superpose eq128204 eq19
    | (have j1 := eq128204 X1 (τ X0)
       grind)
    | exact resolve eq19 eq128204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq128204
  have eq144220 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq144114 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq144114
    | (have j0 := eq144114 X0 X1
       grind)
    | exact resolve eq144114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144114
  have eq144345 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq144220 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq144220
    | (have j0 := eq144220 X0 X1
       grind)
    | exact resolve eq144220 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144220
  have eq144447 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq144345 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq144345
    | (have j0 := eq144345 X0 X1
       grind)
    | exact resolve eq144345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144345
  have eq144540 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq144447 X0 X1
       have i₂ := eq3534 X0
       grind)
    | exact superpose eq3534 eq144447
    | (have j0 := eq144447 X0 X1
       grind)
    | exact resolve eq144447 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3534 eq144447
  have eq150294 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (τ (M.op X1 X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq144540 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144540
    | (have j0 := eq144540 X1 (σ X0)
       grind)
    | exact resolve eq144540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144540
  have eq160417 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq150294 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq150294
    | (have j0 := eq150294 X0 (σ X1)
       grind)
    | exact resolve eq150294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150294
  have eq160666 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq160417 X0 X1
       have i₂ := eq3059 X1
       grind)
    | exact superpose eq3059 eq160417
    | (have j0 := eq160417 X0 X1
       grind)
    | exact resolve eq160417 eq3059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3059 eq160417
  have eq160789 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq160666 X0 X1
       have i₂ := eq3427 X1
       grind)
    | exact superpose eq3427 eq160666
    | (have j0 := eq160666 X0 X1
       grind)
    | exact resolve eq160666 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160666
  have eq160886 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq160789 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq160789
    | (have j0 := eq160789 X0 X1
       grind)
    | exact resolve eq160789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160789
  have eq161753 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq205
       have i₂ := eq160886 x y
       grind)
    | exact superpose eq160886 eq205
    | (have j1 := eq160886 x y
       grind)
    | (have r₁ := eq205
       have r₂ := eq160886 x y
       grind)
    | exact resolve eq205 eq160886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq160886
  have eq161867 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq161753
  have eq161943 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq212 x y
       grind)
    | (have r₁ := eq161867
       have r₂ := eq212 x y
       grind)
    | exact resolve eq161867 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq161867
  have eq162106 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq161943
       have i₂ := eq3084 y
       grind)
    | exact superpose eq3084 eq161943
    | exact resolve eq161943 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161943
  have eq162216 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq162106
       have i₂ := eq3427 y
       grind)
    | exact superpose eq3427 eq162106
    | exact resolve eq162106 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162106
  have eq164492 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq162216
       grind)
    | exact superpose eq162216 eq16
    | exact resolve eq16 eq162216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164514 : (τ (σ y)) ≠ (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq136246 (σ x) (σ y)
       have i₂ := eq162216
       grind)
    | exact superpose eq162216 eq136246
    | (have j0 := eq136246 (σ x) (σ y)
       grind)
    | exact resolve eq136246 eq162216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136246 eq162216
  have eq164517 : (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq164514
  have eq164522 : (σ x) = (σ (k y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq164517
       have i₂ := eq3084 y
       grind)
    | exact superpose eq3084 eq164517
    | exact resolve eq164517 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084 eq164517
  have eq164529 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq164522
       have i₂ := eq3427 y
       grind)
    | exact superpose eq3427 eq164522
    | exact resolve eq164522 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3427 eq164522
  have eq164530 : (σ x) = (σ (M.op y y)) ∨ (τ (σ y)) = (τ (k (σ x) (σ y))) ∨ x = (M.op y y) := by grind
  clear eq164529
  have eq164534 : (τ (σ y)) = (k (τ (σ x)) y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq164530
       have i₂ := eq26 (σ x) y
       grind)
    | exact superpose eq26 eq164530
    | exact resolve eq164530 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq164530
  have eq164536 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq164534
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq164534
    | exact resolve eq164534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164534
  have eq164538 : y = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq164536
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq164536
    | exact resolve eq164536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164536
  have eq165323 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq854 x y
       have i₂ := eq164538
       grind)
    | exact superpose eq164538 eq854
    | (have j0 := eq854 x y
       grind)
    | (have r₁ := eq854 x y
       have r₂ := eq164538
       grind)
    | exact resolve eq854 eq164538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq164538
  have eq165333 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq165323
  have eq165334 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq165333
  have eq167162 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq164492
       have i₂ := eq165334
       grind)
    | exact superpose eq165334 eq164492
    | exact resolve eq164492 eq165334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164492 eq165334
  have eq167163 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq167162
  have eq167164 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq167163
  have eq167178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4109 y
       have i₂ := eq167164
       grind)
    | exact superpose eq167164 eq4109
    | exact resolve eq4109 eq167164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167164
  have eq167271 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq167178
       have r₂ := eq16
       grind)
    | exact resolve eq167178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167178
  have eq168866 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq167271
       grind)
    | exact superpose eq167271 eq10
    | exact resolve eq10 eq167271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167271
  have eq169062 : x = (M.op y y) := by
    first
    | (have i₁ := eq168866
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq168866
    | exact resolve eq168866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168866
  have eq169250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4109 y
       have i₂ := eq169062
       grind)
    | exact superpose eq169062 eq4109
    | exact resolve eq4109 eq169062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109 eq169062
  have eq169346 : False := by grind
  exact eq169346

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X0) X3)) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X3 X2 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq22 X0 X1 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X0 X1 X2 x
       have i₂ := eq22 x X0 X1 X0
       grind)
    | exact superpose eq22 eq51
    | (have j0 := eq51 X0 X1 X2 x
       grind)
    | exact resolve eq51 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq120 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       have j1 := eq68 X1 X1 X0
       grind)
    | (have r₁ := eq114 x X0
       have r₂ := eq68 X0 x x
       grind)
    | (have r₁ := eq114 X0 x
       have r₂ := eq68 X0 X0 x
       grind)
    | (have r₁ := eq114 X0 X0
       have r₂ := eq68 X0 X1 (M.op X0 X0)
       grind)
    | exact resolve eq114 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq114
  have eq455 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq120
  have eq478 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq455 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq484 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (k X2 (k (k (τ X0) X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 (k X0 (σ X1)) X3 X2
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq37
    | exact resolve eq37 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq39
  have eq509 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (M.op X2 (k (k (τ X0) X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq484 X0 X1 X2 X3
       have i₂ := eq478 X2 (k (k (τ X0) X1) X3)
       grind)
    | exact superpose eq478 eq484
    | exact resolve eq484 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq521 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (M.op X2 (M.op (k (τ X0) X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq509 X0 X1 X2 X3
       have i₂ := eq478 (k (τ X0) X1) X3
       grind)
    | exact superpose eq478 eq509
    | exact resolve eq509 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq533 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (M.op X2 (M.op (M.op (τ X0) X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq521 X0 X1 X2 X3
       have i₂ := eq478 (τ X0) X1
       grind)
    | exact superpose eq478 eq521
    | exact resolve eq521 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq544 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq533 X0 X1 X2 X3
       have i₂ := eq22 X3 X1 X2 (τ X0)
       grind)
    | exact superpose eq22 eq533
    | exact resolve eq533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq555 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 X1)) = (M.op (σ X2) (k (k X0 (σ X1)) (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq544 X0 X1 X2 X3
       have i₂ := eq478 (σ X2) (k (k X0 (σ X1)) (σ X3))
       grind)
    | exact superpose eq478 eq544
    | exact resolve eq544 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq564 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 X1)) = (M.op (σ X2) (M.op (k X0 (σ X1)) (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq555 X0 X1 X2 X3
       have i₂ := eq478 (k X0 (σ X1)) (σ X3)
       grind)
    | exact superpose eq478 eq555
    | exact resolve eq555 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq568 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 X1)) = (M.op (σ X2) (M.op (M.op X0 (σ X1)) (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq564 X0 X1 X2 X3
       have i₂ := eq478 X0 (σ X1)
       grind)
    | exact superpose eq478 eq564
    | exact resolve eq564 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq564
  have eq570 : ∀ X1 X2 : G, (M.op (σ X2) (σ X1)) = (σ (M.op X2 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq568 x X1 X2 x
       have i₂ := eq22 (σ x) (σ X1) (σ X2) x
       grind)
    | exact superpose eq22 eq568
    | exact resolve eq568 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq568
  have eq571 : False := by grind
  exact eq571

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_y_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq67 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq74 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq111
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq122 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq140 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq211 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq211
    | exact resolve eq211 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq218 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq218
    | exact resolve eq218 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq238 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
  have eq381 : ∀ X0 : G, (k (M.op (M.op (M.op x y) X0) y) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) (M.op (M.op (M.op x y) X0) y)) := by
    intro X0
    grind
  clear eq213
  have eq386 : ∀ X0 : G, (k (M.op (M.op (M.op x y) X0) y) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq381 x
       have i₂ := eq55 y x (M.op sF0 x) sF0
       grind)
    | exact superpose eq55 eq381
    | exact resolve eq381 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq582 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq10634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10634
    | exact resolve eq10634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10634
  have eq10646 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10635
       have r₂ := eq28
       grind)
    | exact resolve eq10635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10635
  have eq10648 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10646
    | exact resolve eq10646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10646
  have eq10650 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq10648
  have eq10660 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10650
    | exact resolve eq10650 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10650
  have eq10666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10660 eq112
    | exact resolve eq112 eq10660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10660
  have eq10678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10666
  have eq10680 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10678
       have r₂ := eq28
       grind)
    | exact resolve eq10678 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10678
  have eq10796 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10680
  have eq10806 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10796
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10796
    | exact resolve eq10796 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10796
  have eq10809 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq10806
       grind)
    | exact superpose eq10806 eq71
    | exact resolve eq71 eq10806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10806
  have eq10831 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10809
    | exact resolve eq10809 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10809
  have eq10989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10831 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10989
    | exact resolve eq10989 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10989
  have eq11003 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10992
       have r₂ := eq28
       grind)
    | exact resolve eq10992 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10992
  have eq11005 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11003
    | exact resolve eq11003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11003
  have eq11006 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11005
  have eq11009 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11006
  have eq11019 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11009
    | exact resolve eq11009 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11009
  have eq11146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11019 eq10831
    | exact resolve eq10831 eq11019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10831 eq11019
  have eq11152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11146
  have eq11156 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11152
       have r₂ := eq28
       grind)
    | exact resolve eq11152 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11152
  have eq11160 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11156 eq75
    | (have r₁ := eq75
       have r₂ := eq11156
       grind)
    | exact resolve eq75 eq11156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq11156
  have eq11164 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11160
  have eq11602 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11164
  have eq11612 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11602
    | exact resolve eq11602 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11602
  have eq11614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq112 eq11612
    | exact resolve eq11612 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11612 eq112
    | exact resolve eq112 eq11612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq11634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq11619
  have eq11635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11614
  have eq11637 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11634
       have r₂ := eq28
       grind)
    | exact resolve eq11634 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11634
  have eq11638 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq11635
       have r₂ := eq28
       grind)
    | exact resolve eq11635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11635
  have eq11703 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq11638
  have eq11713 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11703
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11703
    | exact resolve eq11703 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11703
  have eq11716 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11713
       grind)
    | exact superpose eq11713 eq71
    | exact resolve eq71 eq11713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11713
  have eq11738 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq11716
    | exact resolve eq11716 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11716
  have eq11767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11738 eq11612
    | exact resolve eq11612 eq11738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11612 eq11738
  have eq11773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq11767
  have eq11780 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11773
       have r₂ := eq28
       grind)
    | exact resolve eq11773 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11773
  have eq11797 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11780 eq29
    | exact resolve eq29 eq11780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11780
  have eq11928 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq11797
    | exact resolve eq11797 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11797
  have eq11929 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11928 eq21
    | exact resolve eq21 eq11928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11938 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11928 eq122
    | exact resolve eq122 eq11928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq11986 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq12031 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11938 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq11938
    | exact resolve eq11938 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq11938
  have eq12038 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11929
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11929
    | exact resolve eq11929 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11929
  have eq12040 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12038 eq27
    | exact resolve eq27 eq12038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12184 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12040 eq55
    | exact resolve eq55 eq12040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12191 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq221 eq12184
    | exact resolve eq12184 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq12184
  have eq12576 : ∀ X0 : G, (k (τ (σ y)) X0) = (τ (k (σ (M.op x y)) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12031 eq238
    | exact resolve eq238 eq12031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12031
  have eq12674 : ∀ X0 : G, (k (τ (σ (M.op x y))) X0) = (k (τ (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12576 x
       have i₂ := eq238 sF1 x
       grind)
    | exact superpose eq238 eq12576
    | exact resolve eq12576 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq12576
  have eq12681 : ∀ X0 : G, (k y X0) = (k (τ (σ (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq12674
    | exact resolve eq12674 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12674
  have eq12686 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31 eq12681
    | exact resolve eq12681 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq12681
  have eq31742 : (τ (σ x)) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11637 eq81
    | exact resolve eq81 eq11637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq11637
  have eq31795 : x = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq31742
    | exact resolve eq31742 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31742
  have eq31801 : y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq31795
       have r₂ := eq74
       grind)
    | exact resolve eq31795 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq31795
  have eq31804 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq31801
  have eq31814 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq31804
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31804
    | exact resolve eq31804 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31804
  have eq31817 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq31814
       grind)
    | exact superpose eq31814 eq71
    | exact resolve eq71 eq31814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31831 : x ≠ (M.op x y) ∨ x = (k y x) := by grind
  clear eq31814
  have eq31844 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq21 eq31817
    | exact resolve eq31817 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31817
  have eq32120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq31844 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq31844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq27 eq32120
    | exact resolve eq32120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32120
  have eq32142 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq32121
       have r₂ := eq28
       grind)
    | exact resolve eq32121 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32121
  have eq32146 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq27 eq32142
    | exact resolve eq32142 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32142
  have eq68043 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq32146
  have eq68053 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq27 eq68043
    | exact resolve eq68043 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68043
  have eq69831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq68053 eq31844
    | exact resolve eq31844 eq68053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31844 eq68053
  have eq69878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq69831
  have eq69887 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq69878
       have r₂ := eq28
       grind)
    | exact resolve eq69878 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69878
  have eq70229 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq69887
       grind)
    | exact superpose eq69887 eq71
    | exact resolve eq71 eq69887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69887
  have eq70285 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70229
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq70229
    | exact resolve eq70229 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70229
  have eq70312 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12038 eq70285
    | exact resolve eq70285 eq12038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70376 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70285 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq70285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70285
  have eq70388 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq70376
    | exact resolve eq70376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70376
  have eq70402 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq70312
       have r₂ := eq28
       grind)
    | exact resolve eq70312 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70312
  have eq70403 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq70388
    | exact resolve eq70388 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70388
  have eq70404 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq70403
  have eq70756 : (τ (σ x)) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70402 eq140
    | exact resolve eq140 eq70402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq70402
  have eq70788 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq70756
    | exact resolve eq70756 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70756
  have eq71253 : x = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70788 eq12686
    | exact resolve eq12686 eq70788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12686 eq70788
  have eq71258 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq71253
  have eq71269 : x = (k y x) := by
    first
    | (have r₁ := eq71258
       have r₂ := eq31831
       grind)
    | exact resolve eq71258 eq31831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31831 eq71258
  have eq71317 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq71269
       grind)
    | exact superpose eq71269 eq71
    | exact resolve eq71 eq71269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71269
  have eq71371 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71317
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq71317
    | exact resolve eq71317 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71317
  have eq72339 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq72349 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71371 eq72339
    | exact resolve eq72339 eq71371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72339
  have eq72350 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq72349
    | exact resolve eq72349 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72349
  have eq72351 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq72350
  have eq72353 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72351 eq28
    | exact resolve eq28 eq72351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72351
  have eq72363 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12038 eq72353
    | (have r₁ := eq72353
       have r₂ := eq12038
       grind)
    | exact resolve eq72353 eq12038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12038 eq72353
  have eq72364 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq72363
  have eq72370 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq72364 eq52
    | exact resolve eq52 eq72364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq78625 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq72370
    | (have j0 := eq72370 (σ y)
       grind)
    | exact resolve eq72370 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79076 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72364 eq78625
    | exact resolve eq78625 eq72364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78625
  have eq79090 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq79076
  have eq79113 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79090 eq12191
    | exact resolve eq12191 eq79090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12191
  have eq79117 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq79090 eq55
    | exact resolve eq55 eq79090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79090
  have eq79124 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq79113
  have eq79127 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79117 x X0
       have i₂ := eq55 X0 sF2 x sF3
       grind)
    | exact superpose eq55 eq79117
    | exact resolve eq79117 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79117
  have eq79618 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ (M.op x y))) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq79124 eq55
    | exact resolve eq55 eq79124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79124
  have eq79626 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79618 x X0
       have i₂ := eq55 X0 sF1 x sF3
       grind)
    | exact superpose eq55 eq79618
    | exact resolve eq79618 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79618
  have eq79644 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq79127
    | (have j0 := eq79127 (σ x)
       grind)
    | exact resolve eq79127 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79127
  have eq79717 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq79644
  have eq79859 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79626 eq72370
    | exact resolve eq72370 eq79626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72370 eq79626
  have eq79868 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq79859
  have eq79875 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq79868
    | exact resolve eq79868 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79868
  have eq79883 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72364 eq79717
    | exact resolve eq79717 eq72364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79717
  have eq79895 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq79883
  have eq79897 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12040 eq79875
    | exact resolve eq79875 eq12040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12040 eq79875
  have eq79909 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq79897
  have eq79914 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72364 eq79909
    | exact resolve eq79909 eq72364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72364 eq79909
  have eq79937 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq79914
  have eq80778 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79895 eq50
    | exact resolve eq50 eq79895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq79895
  have eq81598 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79937 eq80778
    | exact resolve eq80778 eq79937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79937 eq80778
  have eq81762 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq81598
  have eq81775 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq81762
    | exact resolve eq81762 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq81762
  have eq81805 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq81775
       grind)
    | exact superpose eq81775 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq81775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81775
  have eq81806 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq81805
  have eq81846 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq81806
       grind)
    | exact superpose eq81806 eq14
    | exact resolve eq14 eq81806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116640 : (M.op y x) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81846 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81846
    | (have j0 := eq81846 y
       grind)
    | exact resolve eq81846 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81846
  have eq116770 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (M.op y x) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq116640 eq55
    | exact resolve eq55 eq116640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116640
  have eq116779 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq116770 X0 x
       have i₂ := eq55 x x X0 y
       grind)
    | exact superpose eq55 eq116770
    | exact resolve eq116770 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116770
  have eq117654 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11928 eq116779
    | exact resolve eq116779 eq11928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11928 eq116779
  have eq117727 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq117654 X0
       grind)
    | (have r₁ := eq117654 X0
       have r₂ := eq11986
       grind)
    | exact resolve eq117654 eq11986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11986 eq117654
  have eq118544 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117727 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq117727
    | (have j0 := eq117727 x
       grind)
    | exact resolve eq117727 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117727
  have eq118624 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81806
       have i₂ := eq118544
       grind)
    | exact superpose eq118544 eq81806
    | exact resolve eq81806 eq118544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81806 eq118544
  have eq118648 : x = (M.op x y) := by grind
  clear eq118624
  have eq119441 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq118648 eq21
    | exact resolve eq21 eq118648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq119443 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq118648 eq51
    | exact resolve eq51 eq118648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq119446 : (σ (k y x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq118648 eq73
    | exact resolve eq73 eq118648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq119759 : (k (σ y) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq119446
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq119446
    | exact resolve eq119446 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq119446
  have eq119763 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq119441
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq119441
    | exact resolve eq119441 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119441
  have eq119780 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq71371 eq119759
    | exact resolve eq119759 eq71371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71371 eq119759
  have eq119786 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq119763 eq27
    | exact resolve eq27 eq119763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq119951 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq119763 eq70404
    | exact resolve eq70404 eq119763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70404
  have eq120029 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq119951
       have r₂ := eq28
       grind)
    | exact resolve eq119951 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119951
  have eq120098 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq119763 eq119780
    | exact resolve eq119780 eq119763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119780
  have eq125113 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq120029
  have eq125124 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq119786 eq125113
    | exact resolve eq125113 eq119786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125113
  have eq125126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120098 eq125124
    | exact resolve eq125124 eq120098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120098 eq125124
  have eq125128 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq125126
       have r₂ := eq28
       grind)
    | exact resolve eq125126 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125126
  have eq125256 : (k (M.op (M.op (M.op x y) y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq386 (M.op x sF0)
       have i₂ := eq119443 sF0
       grind)
    | exact superpose eq119443 eq386
    | exact resolve eq386 eq119443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq125275 : (k (M.op (M.op x y) y) (M.op x y)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq118648 eq125256
    | exact resolve eq125256 eq118648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125256
  have eq125295 : (k (M.op (M.op x y) y) (M.op x y)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq125275
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq125275
    | exact resolve eq125275 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125275
  have eq125306 : (M.op x (M.op x x)) = (k (M.op x y) x) := by
    first
    | exact superpose eq118648 eq125295
    | exact resolve eq125295 eq118648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125295
  have eq125311 : (k (M.op x y) x) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq125306
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq125306
    | exact resolve eq125306 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125306
  have eq125313 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq125311
       have i₂ := eq119443 x
       grind)
    | exact superpose eq119443 eq125311
    | exact resolve eq125311 eq119443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119443 eq125311
  have eq125315 : (M.op x y) = (k x x) := by
    first
    | exact superpose eq118648 eq125313
    | exact resolve eq125313 eq118648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125313
  have eq125317 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq125315
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq125315
    | exact resolve eq125315 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq125315
  have eq125319 : x = (k x x) := by
    first
    | exact superpose eq118648 eq125317
    | exact resolve eq125317 eq118648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118648 eq125317
  have eq125353 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq582 x x
       have i₂ := eq125319
       grind)
    | exact superpose eq125319 eq582
    | (have j0 := eq582 x x
       grind)
    | exact resolve eq582 eq125319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq125319
  have eq125356 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq125353
  have eq125357 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq125356
  have eq125363 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq125357
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq125357
    | exact resolve eq125357 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq125357
  have eq125384 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq119763 eq125363
    | exact resolve eq125363 eq119763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119763 eq125363
  have eq127322 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq125384 eq14
    | exact resolve eq14 eq125384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130923 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq119786 eq127322
    | exact resolve eq127322 eq119786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127322
  have eq131043 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq125128 eq130923
    | exact resolve eq130923 eq125128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125128 eq130923
  have eq131101 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq131043 eq55
    | exact resolve eq55 eq131043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131043
  have eq131109 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq131101 x X0
       have i₂ := eq55 X0 sF1 x sF3
       grind)
    | exact superpose eq55 eq131101
    | exact resolve eq131101 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq131101
  have eq131173 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq131109 eq119786
    | exact resolve eq119786 eq131109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119786 eq131109
  have eq131202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq125384 eq131173
    | exact resolve eq131173 eq125384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125384 eq131173
  have eq131229 : False := by grind
  exact eq131229
