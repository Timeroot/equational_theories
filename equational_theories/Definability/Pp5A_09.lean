import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq87 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq328 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq107
    | (have j0 := eq107 (σ X0)
       grind)
    | exact resolve eq107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq44
    | (have j1 := eq107 x
       grind)
    | exact resolve eq44 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq397 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq602 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X0 X0) X1 X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq51 (M.op X2 X2) X1 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) X1 X3
       have i₂ := eq55 X1 X0 X2
       grind)
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq647 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq602 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq602
    | exact resolve eq602 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq1025 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq195 X0
       have i₂ := eq51 X0 X1 X2
       grind)
    | (have i₁ := eq195 X2
       have i₂ := eq51 X2 X2 X2
       grind)
    | exact superpose eq51 eq195
    | exact resolve eq195 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3334 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq397 X0 X1 X2
       have i₂ := eq195 X0
       grind)
    | exact superpose eq195 eq397
    | exact resolve eq397 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq397
  have eq7016 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq328 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq30170 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) x) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq606 X0 X1 X2 X3
       have i₂ := eq1025 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq1025 eq606
    | exact resolve eq606 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq1025
  have eq30549 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) x) (M.op x y)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) x) (M.op x y))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X0 X1 x
       have i₂ := eq30170 (M.op X0 X1) X1 X2 x
       grind)
    | exact superpose eq30170 eq647
    | exact resolve eq647 eq30170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq30170
  have eq30803 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq3334 eq30549
    | exact resolve eq30549 eq3334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334 eq30549
  have eq71081 : ∀ X0 : G, y = (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) X0)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq30803 y y x
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq30803
    | exact resolve eq30803 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq71104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71081 x
       have i₂ := eq14 x (M.op x x) x
       grind)
    | exact superpose eq14 eq71081
    | exact resolve eq71081 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71081
  have eq71238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq71104 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq71104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq71238
    | exact resolve eq71238 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71238
  have eq71250 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq71239
       have r₂ := eq28
       grind)
    | exact resolve eq71239 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71239
  have eq71370 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq71250 eq30803
    | exact resolve eq30803 eq71250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71250
  have eq71393 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71370 x
       have i₂ := eq14 sF2 (M.op sF2 sF2) x
       grind)
    | exact superpose eq14 eq71370
    | exact resolve eq71370 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71370
  have eq71535 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq71393
  have eq71711 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq71535
    | exact resolve eq71535 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71535
  have eq72091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq71711 eq71104
    | exact resolve eq71104 eq71711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71104 eq71711
  have eq72093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq72091
  have eq72095 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq72093
       have r₂ := eq28
       grind)
    | exact resolve eq72093 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72093
  have eq72115 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq72095
  have eq72288 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72115
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72115
    | exact resolve eq72115 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72115
  have eq72301 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq72288
       grind)
    | exact superpose eq72288 eq45
    | exact resolve eq45 eq72288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq72288
  have eq72319 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq72301
    | exact resolve eq72301 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72301
  have eq72357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq72319 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq72319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq72357
    | exact resolve eq72357 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72357
  have eq72371 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq72360
       have r₂ := eq28
       grind)
    | exact resolve eq72360 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72360
  have eq240872 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ x)) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq72371 eq30803
    | exact resolve eq30803 eq72371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30803 eq72371
  have eq240915 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq240872 x
       have i₂ := eq14 sF2 (M.op sF2 sF2) x
       grind)
    | exact superpose eq14 eq240872
    | exact resolve eq240872 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240872
  have eq240916 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq240915
  have eq241109 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq240916
  have eq241331 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq241109
    | exact resolve eq241109 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241109
  have eq242598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq241331 eq72319
    | exact resolve eq72319 eq241331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72319 eq241331
  have eq242632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq242598
  have eq242644 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq242632
       have r₂ := eq28
       grind)
    | exact resolve eq242632 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242632
  have eq242647 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq242644 eq30
    | exact resolve eq30 eq242644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq242644
  have eq242815 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq242647
    | exact resolve eq242647 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq242647
  have eq242816 : x = y := by grind
  clear eq242815
  have eq242819 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq242816
       grind)
    | exact superpose eq242816 eq19
    | exact resolve eq19 eq242816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq242820 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq242816
       grind)
    | exact superpose eq242816 eq25
    | exact resolve eq25 eq242816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq242816
  have eq243104 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq242820
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq242820
    | exact resolve eq242820 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242820
  have eq243107 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq243104 eq27
    | exact resolve eq27 eq243104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq243104
  have eq243282 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq332
       have i₂ := eq242819
       grind)
    | exact superpose eq242819 eq332
    | exact resolve eq332 eq242819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq243349 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  have eq243552 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq243282
    | exact resolve eq243282 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243282
  have eq243590 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq248079 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq243552 eq107
    | (have j0 := eq107 (σ x)
       grind)
    | exact resolve eq107 eq243552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq248080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq243107 eq248079
    | exact resolve eq248079 eq243107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248079
  have eq248094 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq248080
       have r₂ := eq28
       grind)
    | exact resolve eq248080 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248080
  have eq248100 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq243107 eq248094
    | exact resolve eq248094 eq243107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248094
  have eq248193 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq248100 eq243590
    | exact resolve eq243590 eq248100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243590 eq248100
  have eq248197 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq243107 eq248193
    | exact resolve eq248193 eq243107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248193
  have eq248574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq248197 eq243552
    | exact resolve eq243552 eq248197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243552 eq248197
  have eq248580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq248574
  have eq248583 : x = (M.op x y) := by
    first
    | (have r₁ := eq248580
       have r₂ := eq28
       grind)
    | exact resolve eq248580 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248580
  have eq248594 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq248583 eq21
    | exact resolve eq21 eq248583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq249007 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq248583 eq243349
    | exact resolve eq243349 eq248583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243349
  have eq249012 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq249007
       have i₂ := eq242819
       grind)
    | exact superpose eq242819 eq249007
    | exact resolve eq249007 eq242819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242819 eq249007
  have eq249193 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq248594
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq248594
    | exact resolve eq248594 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248594
  have eq249196 : x = (k x x) := by
    first
    | exact superpose eq248583 eq249012
    | exact resolve eq249012 eq248583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248583 eq249012
  have eq249826 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7016 x
       have i₂ := eq249196
       grind)
    | exact superpose eq249196 eq7016
    | (have j0 := eq7016 x
       grind)
    | exact resolve eq7016 eq249196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7016 eq249196
  have eq249830 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq249826
  have eq249837 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq249830
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq249830
    | exact resolve eq249830 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq249830
  have eq249855 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq243107 eq249837
    | exact resolve eq249837 eq243107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243107 eq249837
  have eq249871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq249193 eq249855
    | exact resolve eq249855 eq249193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249193 eq249855
  have eq249885 : False := by grind
  exact eq249885

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq175 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq16 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq184 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq552 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq542 X0 X1 X2
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq542
    | exact resolve eq542 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq599 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq182 X0
       have i₂ := eq184 X0
       grind)
    | exact superpose eq184 eq182
    | exact resolve eq182 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq605 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X2
       have i₂ := eq184 X0
       grind)
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq623 : ∀ X0 : G, x = (M.op (M.op (M.op x (σ x)) (M.op (σ x) (σ y))) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq599 eq16
    | exact resolve eq16 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq552 eq16
    | exact resolve eq16 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq599 eq697
    | exact resolve eq697 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq940 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq941 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1022 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1027 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1022 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1022 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq1022 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq1022 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq1022 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1074 : ∀ X0 : G, (M.op (M.op (k X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq1027 X0
       grind)
    | exact superpose eq1027 eq178
    | exact resolve eq178 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1152 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq940
       grind)
    | exact superpose eq940 eq40
    | exact resolve eq40 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq1153 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1152
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1152
    | exact resolve eq1152 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1155 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq1153
    | exact resolve eq1153 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1155 eq941
    | exact resolve eq941 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1170 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1163
       have r₂ := eq27
       grind)
    | exact resolve eq1163 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1175 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1170 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1170
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1170
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1170
       grind)
    | exact resolve eq12 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1175
       have r₂ := eq26
       grind)
    | exact resolve eq1175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1187 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1183
       have i₂ := eq1027 sF2
       grind)
    | exact superpose eq1027 eq1183
    | exact resolve eq1183 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1190 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1155 eq1187
    | exact resolve eq1187 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1191 : (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1190
       have r₂ := eq27
       grind)
    | exact resolve eq1190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1192 : (τ (σ y)) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1191 eq98
    | exact resolve eq98 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1191 eq1074
    | exact resolve eq1074 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1170 eq1195
    | exact resolve eq1195 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170 eq1195
  have eq1199 : (M.op x y) = (M.op y x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq1192
    | exact resolve eq1192 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1200 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1196
       have i₂ := eq1027 sF4
       grind)
    | exact superpose eq1027 eq1196
    | exact resolve eq1196 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1207 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1199
       grind)
    | exact superpose eq1199 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1199
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1199
       grind)
    | exact resolve eq12 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1215 : y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have r₁ := eq1207
       have r₂ := eq18
       grind)
    | exact resolve eq1207 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1221 : y = (k x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1215
       have i₂ := eq1027 x
       grind)
    | exact superpose eq1027 eq1215
    | exact resolve eq1215 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1222 : (M.op x y) = (k y x) ∨ y = (k x x) := by grind
  clear eq1221
  have eq1225 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1200 eq1074
    | exact resolve eq1074 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1226 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1225
       have i₂ := eq1027 sF2
       grind)
    | exact superpose eq1027 eq1225
    | exact resolve eq1225 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1227 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1191 eq1226
    | exact resolve eq1226 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191 eq1226
  have eq1229 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1222
       grind)
    | exact superpose eq1222 eq40
    | exact resolve eq40 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1230 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1229
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1229
    | exact resolve eq1229 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1232 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq20 eq1230
    | exact resolve eq1230 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1244 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq1232 eq941
    | exact resolve eq941 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1251 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq1244
       have r₂ := eq27
       grind)
    | exact resolve eq1244 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1256 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq1251 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1251
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1251
       grind)
    | exact resolve eq12 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1264 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq1256
       have r₂ := eq26
       grind)
    | exact resolve eq1256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1268 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1264
       have i₂ := eq1027 sF2
       grind)
    | exact superpose eq1027 eq1264
    | exact resolve eq1264 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1271 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq1232 eq1268
    | exact resolve eq1268 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232 eq1268
  have eq1272 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq1271
       have r₂ := eq27
       grind)
    | exact resolve eq1271 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1273 : (τ (σ y)) = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq1272 eq98
    | exact resolve eq98 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1272
  have eq1280 : y = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq1273
    | exact resolve eq1273 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1281 : y = (k x x) := by grind
  clear eq1280
  have eq1288 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq40
    | exact resolve eq40 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1289 : x = (M.op (M.op y (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1074 x
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1074
    | exact resolve eq1074 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1290 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1288
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1288
    | exact resolve eq1288 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1292 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1290
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1290
    | exact resolve eq1290 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1310 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op y (σ x))) x) = X0 := by
    intro X0
    first
    | exact superpose eq1289 eq16
    | exact resolve eq16 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1311 : ∀ X0 : G, (M.op (M.op (k X0 X0) (M.op y (σ x))) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1310 X0
       have i₂ := eq1027 X0
       grind)
    | exact superpose eq1027 eq1310
    | exact resolve eq1310 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1341 : x = (M.op (M.op y (M.op y (σ x))) x) := by
    first
    | (have i₁ := eq1311 x
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1311
    | exact resolve eq1311 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1352 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op (k X0 X0) (M.op y (σ x))) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1311 eq599
    | exact resolve eq599 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1372 : (M.op x (M.op x y)) = (M.op (M.op (M.op y (M.op y (σ x))) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1341 eq599
    | exact resolve eq599 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1660 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq175 (M.op X0 X1) (M.op X1 X2) X3
       have i₂ := eq175 X0 X1 X2
       grind)
    | (have i₁ := eq175 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq175 X0 X1 X2
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1668 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x (σ x)) (M.op (σ x) (σ y))) (M.op (M.op x (σ x)) (M.op (σ x) (σ y)))) (M.op (M.op (M.op x (σ x)) (M.op (σ x) (σ y))) (M.op (M.op x (σ x)) (M.op (σ x) (σ y))))) = (M.op x (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq623 eq175
    | exact resolve eq175 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq1670 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) (M.op y (σ x))) (M.op (k X0 X0) (M.op y (σ x)))) (M.op (M.op (k X0 X0) (M.op y (σ x))) (M.op (k X0 X0) (M.op y (σ x))))) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq1311 eq175
    | exact resolve eq175 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1673 : ∀ X0 : G, (M.op (M.op (M.op y (M.op y (σ x))) (M.op y (M.op y (σ x)))) (M.op (M.op y (M.op y (σ x))) (M.op y (M.op y (σ x))))) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1341 eq175
    | exact resolve eq175 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1682 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ x) (σ y) X0
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1835 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1682 X0
       have i₂ := eq710 sF2 sF2 sF2
       grind)
    | exact superpose eq710 eq1682
    | (have j1 := eq710 (σ x) (σ y) X0
       grind)
    | exact resolve eq1682 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682
  have eq1843 : ∀ X0 : G, (M.op (M.op (M.op y (M.op y (σ x))) (σ x)) (M.op (σ x) (σ y))) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1673 X0
       have i₂ := eq710 (M.op y (M.op y sF2)) (M.op y (M.op y sF2)) (M.op y (M.op y sF2))
       grind)
    | exact superpose eq710 eq1673
    | exact resolve eq1673 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq1846 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) (M.op y (σ x))) (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1670 X0 X1
       have i₂ := eq710 (M.op (k X0 X0) (M.op y sF2)) (M.op (k X0 X0) (M.op y sF2)) (M.op (k X0 X0) (M.op y sF2))
       grind)
    | exact superpose eq710 eq1670
    | exact resolve eq1670 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq1848 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq605 eq1668
    | exact resolve eq1668 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq1668
  have eq1856 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1660 X0 X1 X2 X3
       have i₂ := eq710 X0 X0 X0
       grind)
    | exact superpose eq710 eq1660
    | exact resolve eq1660 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1906 : ∀ X0 : G, (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1835 X0
       have i₂ := eq1027 sF2
       grind)
    | exact superpose eq1027 eq1835
    | exact resolve eq1835 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1912 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1372 eq1843
    | exact resolve eq1843 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372 eq1843
  have eq1914 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq1352 eq1846
    | exact resolve eq1846 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352 eq1846
  have eq1915 : ∀ X0 X1 : G, (k x x) = (M.op x (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1848 X0 X1
       have i₂ := eq1027 x
       grind)
    | exact superpose eq1027 eq1848
    | exact resolve eq1848 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq1922 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1856 X0 X1 X2 X3
       have i₂ := eq710 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq710 eq1856
    | exact resolve eq1856 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq1944 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq1292 eq1906
    | exact resolve eq1906 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906
  have eq1947 : ∀ X0 X1 : G, y = (M.op x (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1915 X0 X1
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1915
    | exact resolve eq1915 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915
  have eq1961 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1227 eq1944
    | exact resolve eq1944 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1971 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | exact superpose eq1944 eq552
    | exact resolve eq552 eq1944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq1973 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | exact superpose eq599 eq1971
    | exact resolve eq1971 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq1979 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1961
       have i₂ := eq1027 sF4
       grind)
    | exact superpose eq1027 eq1961
    | exact resolve eq1961 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq1981 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1922 eq1973
    | exact resolve eq1973 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922 eq1973
  have eq1983 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1200 eq1979
    | exact resolve eq1979 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq1989 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op y (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq599 y
       have i₂ := eq1983
       grind)
    | exact superpose eq1983 eq599
    | exact resolve eq599 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2004 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1289 eq1989
    | exact resolve eq1989 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq2011 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2004
       have i₂ := eq1027 sF0
       grind)
    | exact superpose eq1027 eq2004
    | exact resolve eq2004 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq2127 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) x) (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1981 eq552
    | exact resolve eq552 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2142 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq599 eq2127
    | exact resolve eq2127 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq2127
  have eq2146 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1981 eq2142
    | exact resolve eq2142 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981 eq2142
  have eq2147 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq2146
       have i₂ := eq1027 sF4
       grind)
    | exact superpose eq1027 eq2146
    | exact resolve eq2146 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2168 : ∀ X0 : G, y = (M.op x (M.op (k (M.op x y) (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq1947 sF0 x
       have i₂ := eq1027 sF0
       grind)
    | exact superpose eq1027 eq1947
    | exact resolve eq1947 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq2199 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2011 eq2168
    | exact resolve eq2168 eq2011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2218 : y = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2199 x
       have i₂ := eq1912 x
       grind)
    | (have i₁ := eq2199 y
       have i₂ := eq1912 x
       grind)
    | exact superpose eq1912 eq2199
    | (have j0 := eq2199 y
       grind)
    | exact resolve eq2199 eq1912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912 eq2199
  have eq2251 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq2168 eq1914
    | exact resolve eq1914 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168
  have eq2267 : (M.op x (M.op x y)) = (k (M.op x x) x) := by
    first
    | (have i₁ := eq181 x
       have i₂ := eq1914 x x
       grind)
    | exact superpose eq1914 eq181
    | exact resolve eq181 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq1914
  have eq2327 : (M.op x (M.op x y)) = (k (k x x) x) := by
    first
    | (have i₁ := eq2267
       have i₂ := eq1027 x
       grind)
    | exact superpose eq1027 eq2267
    | exact resolve eq2267 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq2344 : (k y x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2327
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq2327
    | exact resolve eq2327 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327
  have eq2387 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2251 x
       grind)
    | exact superpose eq2251 eq18
    | (have j1 := eq2251 x
       grind)
    | exact resolve eq18 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2251
  have eq2439 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2387 eq2218
    | exact resolve eq2218 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218
  have eq2454 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2439 eq27
    | exact resolve eq27 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2459 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2439 eq1200
    | exact resolve eq1200 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq2468 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2439 eq2147
    | exact resolve eq2147 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2469 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1292 eq2468
    | exact resolve eq2468 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468
  have eq2473 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1292 eq2459
    | exact resolve eq2459 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459
  have eq2476 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2469
    | exact resolve eq2469 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469
  have eq2480 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2439 eq2476
    | exact resolve eq2476 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439 eq2476
  have eq2488 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2480 eq32
    | exact resolve eq32 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2501 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2480 eq1155
    | exact resolve eq1155 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq2480
  have eq2529 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1292 eq2501
    | exact resolve eq2501 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501
  have eq2542 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq2488
    | exact resolve eq2488 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2488
  have eq2555 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2473 eq2529
    | exact resolve eq2529 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473 eq2529
  have eq2567 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2555
       have r₂ := eq2454
       grind)
    | exact resolve eq2555 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454 eq2555
  have eq2577 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2542 eq2567
    | exact resolve eq2567 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542 eq2567
  have eq2585 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2577
       have i₂ := eq1027 x
       grind)
    | exact superpose eq1027 eq2577
    | exact resolve eq2577 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq2589 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2585
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq2585
    | exact resolve eq2585 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq2585
  have eq2590 : y = (M.op x y) := by grind
  clear eq2589
  have eq2594 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2590
       grind)
    | exact superpose eq2590 eq24
    | exact resolve eq24 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2600 : x = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1289
       have i₂ := eq2590
       grind)
    | exact superpose eq2590 eq1289
    | exact resolve eq1289 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq2606 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1983
       have i₂ := eq2590
       grind)
    | exact superpose eq2590 eq1983
    | exact resolve eq1983 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq2615 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2594 eq20
    | exact resolve eq20 eq2594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2722 : (M.op x y) = (k y x) := by
    first
    | exact superpose eq2344 eq2387
    | exact resolve eq2387 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344 eq2387
  have eq2741 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq2722
       have i₂ := eq2590
       grind)
    | exact superpose eq2590 eq2722
    | exact resolve eq2722 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590 eq2722
  have eq2757 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2741 eq40
    | exact resolve eq40 eq2741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2741
  have eq2758 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq2757
    | exact resolve eq2757 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757
  have eq2760 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2615 eq2758
    | exact resolve eq2758 eq2615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758
  have eq2769 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2760 eq941
    | exact resolve eq941 eq2760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq2760
  have eq3325 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2606 eq552
    | exact resolve eq552 eq2606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq2606
  have eq3329 : (M.op x y) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3325 x
       have i₂ := eq710 sF0 sF0 x
       grind)
    | exact superpose eq710 eq3325
    | exact resolve eq3325 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq3325
  have eq3340 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2600 eq3329
    | exact resolve eq3329 eq2600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600 eq3329
  have eq3352 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3340 eq27
    | exact resolve eq27 eq3340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3366 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3340 eq2147
    | exact resolve eq2147 eq3340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2147
  have eq3368 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1292 eq3366
    | exact resolve eq3366 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366
  have eq3376 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2615 eq3352
    | exact resolve eq3352 eq2615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615 eq3352
  have eq3377 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3368
    | exact resolve eq3368 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3368
  have eq3382 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3340 eq3377
    | exact resolve eq3377 eq3340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3340 eq3377
  have eq3387 : x = (M.op x y) := by
    first
    | (have r₁ := eq3382
       have r₂ := eq3376
       grind)
    | exact resolve eq3382 eq3376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376 eq3382
  have eq3391 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq3387
       grind)
    | exact superpose eq3387 eq22
    | exact resolve eq22 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3387
  have eq3454 : (σ x) = (σ y) := by
    first
    | exact superpose eq3391 eq2594
    | exact resolve eq2594 eq3391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq3455 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3391 eq20
    | exact resolve eq20 eq3391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3391
  have eq3557 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3454 eq2769
    | exact resolve eq2769 eq3454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769
  have eq3558 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3557
       have i₂ := eq1027 sF2
       grind)
    | exact superpose eq1027 eq3557
    | exact resolve eq3557 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027 eq3557
  have eq3586 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1292 eq3558
    | exact resolve eq3558 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292 eq3558
  have eq3608 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3454 eq3586
    | exact resolve eq3586 eq3454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454 eq3586
  have eq3609 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3608
  have eq3667 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq3609 eq27
    | exact resolve eq27 eq3609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3609
  have eq3695 : False := by grind
  exact eq3695

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq831 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq10286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10286
    | exact resolve eq10286 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10286
  have eq10298 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10287
       have r₂ := eq28
       grind)
    | exact resolve eq10287 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10287
  have eq10300 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10298
    | exact resolve eq10298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10298
  have eq10306 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq10300
  have eq10364 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10306
    | exact resolve eq10306 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10306
  have eq10370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10364 eq113
    | exact resolve eq113 eq10364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10364
  have eq10378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10370
  have eq10380 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10378
       have r₂ := eq28
       grind)
    | exact resolve eq10378 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10378
  have eq10389 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10380
  have eq10447 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10389
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10389
    | exact resolve eq10389 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10389
  have eq10605 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq10447
       grind)
    | exact superpose eq10447 eq72
    | exact resolve eq72 eq10447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10447
  have eq10619 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10605
    | exact resolve eq10605 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10605
  have eq10632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10619 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10632
    | exact resolve eq10632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10632
  have eq10646 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10635
       have r₂ := eq28
       grind)
    | exact resolve eq10635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10635
  have eq10648 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10646
    | exact resolve eq10646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10646
  have eq10649 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10648
  have eq10656 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10649
  have eq10714 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq10656
    | exact resolve eq10656 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10656
  have eq10728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10714 eq10619
    | exact resolve eq10619 eq10714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10619 eq10714
  have eq10730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10728
  have eq10734 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10730
       have r₂ := eq28
       grind)
    | exact resolve eq10730 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10730
  have eq10886 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10734 eq28
    | exact resolve eq28 eq10734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10888 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10734 eq76
    | (have r₁ := eq76
       have r₂ := eq10734
       grind)
    | exact resolve eq76 eq10734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq10734
  have eq10897 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq10888
  have eq11122 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10897 eq113
    | exact resolve eq113 eq10897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11137 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq11122
  have eq11151 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11137
       have r₂ := eq10886
       grind)
    | exact resolve eq11137 eq10886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11137
  have eq11161 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq11151
  have eq11221 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11161
    | exact resolve eq11161 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11161
  have eq11496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11221 eq113
    | exact resolve eq113 eq11221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq11221
  have eq11508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11496
  have eq11512 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11508
       have r₂ := eq28
       grind)
    | exact resolve eq11508 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11508
  have eq11521 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq11512
  have eq11581 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11521
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11521
    | exact resolve eq11521 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11521
  have eq11717 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11581
       grind)
    | exact superpose eq11581 eq72
    | exact resolve eq72 eq11581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11581
  have eq11731 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq11717
    | exact resolve eq11717 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11717
  have eq11748 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11731 eq10897
    | exact resolve eq10897 eq11731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10897
  have eq11752 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11748
  have eq11760 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11752
       have r₂ := eq10886
       grind)
    | exact resolve eq11752 eq10886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10886 eq11752
  have eq11920 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11760
  have eq11980 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11920
    | exact resolve eq11920 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11920
  have eq11998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11980 eq11731
    | exact resolve eq11731 eq11980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11731 eq11980
  have eq12000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11998
  have eq12008 : y = (M.op x y) := by
    first
    | (have r₁ := eq12000
       have r₂ := eq28
       grind)
    | exact resolve eq12000 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12000
  have eq12011 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq12008 eq21
    | exact resolve eq21 eq12008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq12017 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq12008 eq75
    | (have r₁ := eq75
       have r₂ := eq12008
       grind)
    | exact resolve eq75 eq12008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq12078 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq12017
  have eq12130 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12011
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12011
    | exact resolve eq12011 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12011
  have eq12131 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq12130 eq27
    | exact resolve eq27 eq12130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq15805 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq12078
       grind)
    | exact superpose eq12078 eq72
    | exact resolve eq72 eq12078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15814 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq831 x y
       have i₂ := eq12078
       grind)
    | exact superpose eq12078 eq831
    | (have j0 := eq831 x y
       grind)
    | exact resolve eq831 eq12078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12078
  have eq15817 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq15814
  have eq15824 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15817
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15817
    | exact resolve eq15817 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15817
  have eq15831 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12130 eq15805
    | exact resolve eq15805 eq12130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15805
  have eq15833 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12130 eq15824
    | exact resolve eq15824 eq12130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15824
  have eq15840 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15831
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15831
    | exact resolve eq15831 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15831
  have eq15841 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15833
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15833
    | exact resolve eq15833 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15833
  have eq15847 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12130 eq15840
    | exact resolve eq15840 eq12130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15840
  have eq15848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12131 eq15841
    | exact resolve eq15841 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15841
  have eq15849 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15848
       have r₂ := eq28
       grind)
    | exact resolve eq15848 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15848
  have eq15850 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15849
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15849
    | exact resolve eq15849 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15849
  have eq15851 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15850
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15850
    | exact resolve eq15850 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15850
  have eq15852 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12130 eq15851
    | exact resolve eq15851 eq12130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15851
  have eq15907 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq15852
  have eq15990 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12131 eq15907
    | exact resolve eq15907 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15907
  have eq16296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15990 eq15847
    | exact resolve eq15847 eq15990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15847 eq15990
  have eq16299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq16296
  have eq16301 : y = (M.op x x) := by
    first
    | (have r₁ := eq16299
       have r₂ := eq28
       grind)
    | exact resolve eq16299 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16299
  have eq16319 : (M.op x y) = (k y x) := by grind
  clear eq16301
  have eq16408 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16319
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16319
    | exact resolve eq16319 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16319
  have eq16421 : y = (k y x) := by
    first
    | exact superpose eq12008 eq16408
    | exact resolve eq16408 eq12008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12008 eq16408
  have eq16429 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq16421
       grind)
    | exact superpose eq16421 eq72
    | exact resolve eq72 eq16421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq16438 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq831 x y
       have i₂ := eq16421
       grind)
    | exact superpose eq16421 eq831
    | (have j0 := eq831 x y
       grind)
    | exact resolve eq831 eq16421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq16421
  have eq16441 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq16438
  have eq16447 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16441
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16441
    | exact resolve eq16441 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16441
  have eq16454 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq12130 eq16429
    | exact resolve eq16429 eq12130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16429
  have eq16455 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12130 eq16447
    | exact resolve eq16447 eq12130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16447
  have eq16462 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq16454
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16454
    | exact resolve eq16454 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16454
  have eq16463 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16455
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16455
    | exact resolve eq16455 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16455
  have eq16469 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq12130 eq16462
    | exact resolve eq16462 eq12130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16462
  have eq16470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12131 eq16463
    | exact resolve eq16463 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16463
  have eq16471 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq16470
       have r₂ := eq28
       grind)
    | exact resolve eq16470 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16470
  have eq16472 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16471
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16471
    | exact resolve eq16471 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16471
  have eq16473 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16472
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16472
    | exact resolve eq16472 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16472
  have eq16474 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12130 eq16473
    | exact resolve eq16473 eq12130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12130 eq16473
  have eq16531 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq16474
  have eq16611 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq12131 eq16531
    | exact resolve eq16531 eq12131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12131 eq16531
  have eq16619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16469 eq16611
    | exact resolve eq16611 eq16469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16469 eq16611
  have eq16620 : False := by grind
  exact eq16620

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pxy_Equation2045 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq86 : x ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y y) := by
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
  have eq87 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq98 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq94
  have eq99 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq98
  have eq130 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq16
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X0) X1 X2
       have i₂ := eq53 X0 X1 X2
       grind)
    | (have i₁ := eq53 (M.op X2 X2) X1 X2
       have i₂ := eq53 X2 X2 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op X0 X0) (σ x))) (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op X0 X0) (σ x)))) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq761 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq745 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq745
    | exact resolve eq745 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq807
    | exact resolve eq807 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq811 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq808
       have r₂ := eq28
       grind)
    | exact resolve eq808 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq813 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq811
    | exact resolve eq811 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq816 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq813 eq87
    | (have r₁ := eq87
       have r₂ := eq813
       grind)
    | exact resolve eq87 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq813
  have eq819 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq816
  have eq820 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq819
  have eq891 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq820 eq61
    | exact resolve eq61 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq820
  have eq898 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq130 eq891
    | exact resolve eq891 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq891
  have eq901 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq898
       have r₂ := eq86
       grind)
    | exact resolve eq898 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq898
  have eq904 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq901
       grind)
    | exact superpose eq901 eq49
    | exact resolve eq49 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq905 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq901
       grind)
    | exact superpose eq901 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq906 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq905
  have eq908 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq906
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq906
    | exact resolve eq906 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq909 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq904
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq904
    | exact resolve eq904 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq904
  have eq911 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq908
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq908
    | exact resolve eq908 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq917 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq909 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq918 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq917
  have eq922 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq918
    | exact resolve eq918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq925 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq922
    | exact resolve eq922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq954 : ∀ X0 X1 : G, (M.op x y) = (M.op y (M.op (M.op (M.op x y) X0) X1)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 y X1 x
       have i₂ := eq911
       grind)
    | exact superpose eq911 eq54
    | exact resolve eq54 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq955 : y = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55 y
       have i₂ := eq911
       grind)
    | exact superpose eq911 eq55
    | exact resolve eq55 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq978 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212 X0
       have i₂ := eq53 X0 X1 X2
       grind)
    | (have i₁ := eq212 X2
       have i₂ := eq53 X2 X2 X2
       grind)
    | exact superpose eq53 eq212
    | exact resolve eq212 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1011 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq925 eq14
    | exact resolve eq14 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq925 eq55
    | exact resolve eq55 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq925
  have eq1515 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq761 X0
       have i₂ := eq212 x
       grind)
    | exact superpose eq212 eq761
    | exact resolve eq761 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq1715 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq762 X0
       have i₂ := eq212 sF2
       grind)
    | exact superpose eq212 eq762
    | exact resolve eq762 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq1729 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq954 eq1515
    | exact resolve eq1515 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq1515
  have eq3583 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq528 X0 X1 X2
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq528
    | exact resolve eq528 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq3705 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1729 eq3583
    | exact resolve eq3583 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq3740 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq1715 eq3583
    | exact resolve eq3583 eq1715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq3779 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3705
       have i₂ := eq212 sF0
       grind)
    | exact superpose eq212 eq3705
    | exact resolve eq3705 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3705
  have eq3844 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3779 eq955
    | exact resolve eq955 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq3779
  have eq3861 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3844
  have eq3866 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3861 eq30
    | exact resolve eq30 eq3861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3861
  have eq3885 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq3866
    | exact resolve eq3866 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3866
  have eq3886 : x = (M.op x y) ∨ x = y := by grind
  clear eq3885
  have eq3889 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3886 eq21
    | exact resolve eq21 eq3886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3930 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq3889
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3889
    | exact resolve eq3889 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq18283 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (M.op (M.op X0 X0) (σ x)) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq754 X0 X1
       have i₂ := eq212 (M.op (M.op X0 X0) sF2)
       grind)
    | exact superpose eq212 eq754
    | exact resolve eq754 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq754
  have eq18561 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) x) (M.op x y)) (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) x) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq18283 eq804
    | exact resolve eq804 eq18283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq18283
  have eq18674 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq3583 eq18561
    | exact resolve eq18561 eq3583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3583 eq18561
  have eq32932 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1011 eq18674
    | exact resolve eq18674 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011 eq18674
  have eq40002 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3930 eq32932
    | exact resolve eq32932 eq3930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32932
  have eq40061 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq40002
  have eq40064 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq40061
       have r₂ := eq28
       grind)
    | exact resolve eq40061 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40061
  have eq71041 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq40064 eq3740
    | exact resolve eq3740 eq40064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740 eq40064
  have eq71271 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq71041
       have i₂ := eq978 sF4 sF4 sF4
       grind)
    | exact superpose eq978 eq71041
    | exact resolve eq71041 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978 eq71041
  have eq71286 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq71271 eq1014
    | exact resolve eq1014 eq71271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq71271
  have eq71364 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq71286
  have eq72078 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq71364 eq28
    | exact resolve eq28 eq71364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71364
  have eq72216 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq72078
       have r₂ := eq3930
       grind)
    | exact resolve eq72078 eq3930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72078
  have eq72287 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq72216
  have eq72332 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq72287
       have r₂ := eq3930
       grind)
    | exact resolve eq72287 eq3930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3930 eq72287
  have eq72367 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq72332 eq30
    | exact resolve eq30 eq72332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq72332
  have eq72573 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq72367
    | exact resolve eq72367 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq72367
  have eq72700 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq72573 eq3886
    | exact resolve eq3886 eq72573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3886 eq72573
  have eq73043 : x = y := by grind
  clear eq72700
  have eq73201 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq73043
       grind)
    | exact superpose eq73043 eq19
    | exact resolve eq19 eq73043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq73202 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq73043
       grind)
    | exact superpose eq73043 eq25
    | exact resolve eq25 eq73043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq73043
  have eq73334 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq73202
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq73202
    | exact resolve eq73202 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq73202
  have eq73355 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq73334 eq27
    | exact resolve eq27 eq73334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq73334
  have eq73713 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq73355 eq69
    | exact resolve eq69 eq73355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq73355
  have eq73893 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq73713
       have i₂ := eq73201
       grind)
    | exact superpose eq73201 eq73713
    | exact resolve eq73713 eq73201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73201 eq73713
  have eq73911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq73893 eq15
    | exact resolve eq15 eq73893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73893
  have eq73987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq73911
    | exact resolve eq73911 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq73911
  have eq74008 : False := by grind
  exact eq74008

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_x_pyx_pxy_pyx_Equation2046 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq14 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (M.op x y)) := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq77 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq100 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq103 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq77 sF3 (σ X0)
       grind)
    | exact superpose eq77 eq36
    | (have j1 := eq77 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq77 y x
       grind)
    | exact superpose eq77 eq100
    | (have j1 := eq77 y x
       grind)
    | exact resolve eq100 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
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
  have eq124 : y ≠ (M.op x y) ∨ (M.op x x) = (M.op y x) ∨ (M.op y x) = (k y x) := by
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
  have eq125 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq77
    | (have j0 := eq77 (σ y) (σ x)
       grind)
    | exact resolve eq77 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq138
    | exact resolve eq138 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq142 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq139
       have r₂ := eq27
       grind)
    | exact resolve eq139 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq144 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq142
    | exact resolve eq142 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq154 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq156 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq159 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq156
       have i₂ := eq66 sF1
       grind)
    | exact superpose eq66 eq156
    | exact resolve eq156 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq161 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq159
       have i₂ := eq66 sF0
       grind)
    | exact superpose eq66 eq159
    | exact resolve eq159 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq182 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq154 eq16
    | exact resolve eq16 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq197 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq161 eq16
    | exact resolve eq16 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq253 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq282 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq34
    | exact resolve eq34 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq293 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq282
    | exact resolve eq282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq295 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq293 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq293
    | exact resolve eq293 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq293
  have eq393 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq451 : ∀ X0 : G, (M.op (M.op x x) x) = (M.op (M.op x y) (M.op X0 (M.op (M.op x x) x))) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq567 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq144 eq125
    | (have r₁ := eq125
       have r₂ := eq144
       grind)
    | exact resolve eq125 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq568 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq567
  have eq571 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq568 eq117
    | exact resolve eq117 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq574 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq571
  have eq583 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq574 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq574
       grind)
    | exact resolve eq13 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq586 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq583
  have eq587 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq586
    | exact resolve eq586 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq587 eq117
    | exact resolve eq117 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq654 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq651
  have eq658 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq654
       have r₂ := eq27
       grind)
    | exact resolve eq654 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq664 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq658 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) X0) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq658 eq14
    | exact resolve eq14 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq664
    | exact resolve eq664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq1911 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (σ x)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq665 sF2
       have i₂ := eq393 sF2 x
       grind)
    | (have i₁ := eq665 sF2
       have i₂ := eq393 sF2 sF2
       grind)
    | exact superpose eq393 eq665
    | exact resolve eq665 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq2046 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1911
    | (have j0 := eq1911 (σ y)
       grind)
    | exact resolve eq1911 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq2057 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq144 eq2046
    | exact resolve eq2046 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq2046
  have eq2065 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq2057
  have eq2066 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq658 eq2065
    | exact resolve eq2065 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq2065
  have eq2076 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq2066
  have eq2080 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2076 eq197
    | exact resolve eq197 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq2076
  have eq2100 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq2080
    | exact resolve eq2080 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2080
  have eq2101 : ∀ X0 : G, (M.op x y) = (M.op (M.op x X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2100 eq253
    | exact resolve eq253 eq2100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq2103 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2100 eq393
    | exact resolve eq393 eq2100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2110 : ∀ X0 : G, (M.op x y) = (M.op (M.op x X0) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2100 eq14
    | exact resolve eq14 eq2100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2264 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2101 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2101
    | (have j0 := eq2101 y
       grind)
    | exact resolve eq2101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2770 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2264 eq2103
    | exact resolve eq2103 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103 eq2264
  have eq2787 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2770
  have eq2790 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2787 eq2100
    | exact resolve eq2100 eq2787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100 eq2787
  have eq2808 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2790
  have eq2811 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2808 eq2110
    | exact resolve eq2110 eq2808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110 eq2808
  have eq2821 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq2811
  have eq2868 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq2821
       grind)
    | exact superpose eq2821 eq72
    | exact resolve eq72 eq2821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2821
  have eq2890 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2868
    | exact resolve eq2868 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868
  have eq2891 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2890 eq667
    | (have r₁ := eq667
       have r₂ := eq2890
       grind)
    | exact resolve eq667 eq2890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq2890
  have eq2919 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2891
  have eq2920 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2919
  have eq2989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2920 eq117
    | exact resolve eq117 eq2920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq2920
  have eq2992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2989
  have eq2996 : y = (M.op x y) := by
    first
    | (have r₁ := eq2992
       have r₂ := eq27
       grind)
    | exact resolve eq2992 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq2998 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2996 eq20
    | exact resolve eq20 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3002 : y ≠ y ∨ (M.op x x) = (M.op y x) ∨ (M.op y x) = (k y x) := by
    first
    | exact superpose eq2996 eq124
    | (have r₁ := eq124
       have r₂ := eq2996
       grind)
    | exact resolve eq124 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq3010 : (M.op x x) = (M.op y x) ∨ (M.op y x) = (k y x) := by grind
  clear eq3002
  have eq3019 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2998
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2998
    | exact resolve eq2998 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2998
  have eq3079 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3019 eq26
    | exact resolve eq26 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3412 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq3019 eq103
    | (have j0 := eq103 X0
       grind)
    | exact resolve eq103 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3413 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3019 eq3412
    | (have j0 := eq3412 X0
       grind)
    | exact resolve eq3412 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412
  have eq3455 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3413 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3413
    | (have j0 := eq3413 x
       grind)
    | exact resolve eq3413 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3413
  have eq3476 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3079 eq3455
    | exact resolve eq3455 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3455
  have eq3499 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3476
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq3476
    | exact resolve eq3476 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq3476
  have eq3514 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3019 eq3499
    | exact resolve eq3499 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3499
  have eq3520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq3079 eq3514
    | exact resolve eq3514 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514
  have eq3523 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq3520
       have r₂ := eq27
       grind)
    | exact resolve eq3520 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3520
  have eq3529 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq3523 eq182
    | exact resolve eq182 eq3523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq3523
  have eq3531 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2996 eq3529
    | exact resolve eq3529 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3529
  have eq4135 : ∀ X0 : G, (M.op (M.op x x) x) = (M.op y (M.op X0 (M.op (M.op x x) x))) := by
    intro X0
    first
    | exact superpose eq2996 eq451
    | exact resolve eq451 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq4141 : (M.op y x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq4135 (M.op (M.op x x) x)
       have i₂ := eq14 x x (M.op x x)
       grind)
    | exact superpose eq14 eq4135
    | exact resolve eq4135 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135
  have eq4166 : ∀ X0 : G, x = (M.op (M.op y x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq4141
       grind)
    | exact superpose eq4141 eq14
    | exact resolve eq14 eq4141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4141
  have eq10182 : (M.op x x) = (M.op y x) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3010
       have i₂ := eq3531
       grind)
    | exact superpose eq3531 eq3010
    | exact resolve eq3010 eq3531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3010
  have eq10191 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq10182
       grind)
    | exact superpose eq10182 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10182
       grind)
    | exact resolve eq13 eq10182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10182
  have eq10199 : (M.op x y) = (k y x) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq10191
  have eq10200 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10199
       have i₂ := eq3531
       grind)
    | exact superpose eq3531 eq10199
    | exact resolve eq10199 eq3531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10199
  have eq10203 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10200
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10200
    | exact resolve eq10200 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10200
  have eq10205 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2996 eq10203
    | exact resolve eq10203 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10203
  have eq10214 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4166 y
       have i₂ := eq10205
       grind)
    | exact superpose eq10205 eq4166
    | exact resolve eq4166 eq10205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166
  have eq10217 : (M.op x x) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq10205
       grind)
    | exact superpose eq10205 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq10205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10205
  have eq10224 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x x) ≠ (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10217
       have i₂ := eq3531
       grind)
    | exact superpose eq3531 eq10217
    | exact resolve eq10217 eq3531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3531 eq10217
  have eq10227 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x x) ≠ (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10224
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10224
    | exact resolve eq10224 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10224
  have eq10229 : y = (τ (M.op (σ x) (σ y))) ∨ (M.op x x) ≠ (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2996 eq10227
    | exact resolve eq10227 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996 eq10227
  have eq10230 : (M.op x x) ≠ (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq10229
  have eq10493 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq10214 eq295
    | exact resolve eq295 eq10214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq10214
  have eq10524 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10493
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10493
    | exact resolve eq10493 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10493
  have eq10553 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq10524 eq393
    | exact resolve eq393 eq10524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq10562 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq10524 eq14
    | exact resolve eq14 eq10524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10843 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3079 eq10562
    | (have j0 := eq10562 (σ y)
       grind)
    | exact resolve eq10562 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3079
  have eq12759 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq10843 eq10553
    | exact resolve eq10553 eq10843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10553 eq10843
  have eq12792 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq12759
  have eq12804 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12792 eq10524
    | exact resolve eq10524 eq12792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10524 eq12792
  have eq12838 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq12804
  have eq12852 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12838 eq10562
    | exact resolve eq10562 eq12838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10562 eq12838
  have eq12865 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq12852
  have eq13039 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq12865 eq71
    | exact resolve eq71 eq12865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq12865
  have eq13089 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq13039
       have r₂ := eq10230
       grind)
    | exact resolve eq13039 eq10230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10230 eq13039
  have eq13092 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13089 eq15
    | exact resolve eq15 eq13089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13089
  have eq13144 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13092
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13092
    | exact resolve eq13092 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13092
  have eq13149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3019 eq13144
    | exact resolve eq13144 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3019 eq13144
  have eq13150 : False := by grind
  exact eq13150

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pyy_pxy_Equation2046 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
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
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq132 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq16 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X2 (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) (M.op x X0) X2
       have i₂ := eq16 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (σ y) = (M.op (M.op (k (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq178
    | exact resolve eq178 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq183 : ∀ X0 X2 : G, (k X0 X0) = (M.op X0 (M.op X2 (k X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq176 X0 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq184 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (k X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq175
    | exact resolve eq175 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq186 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op X0 X0)
       have i₂ := eq174 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) (M.op X0 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq174 (M.op X0 X0)
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (M.op (k (k X0 X0) (k X0 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq189
    | exact resolve eq189 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq191 : ∀ X0 : G, (k (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq188
    | exact resolve eq188 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq332 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq416 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq332 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq332
    | exact resolve eq332 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq519 : ∀ X0 : G, (τ (k (k (σ y) (σ y)) X0)) = (k (k y y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq115 eq416
    | exact resolve eq416 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (M.op X1 (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq183 (σ X1) x
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq183
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq187 (M.op (k X0 X0) X0) X1
       have i₂ := eq191 X0
       grind)
    | exact superpose eq191 eq187
    | exact resolve eq187 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, (M.op (τ (k X0 X0)) (τ X0)) = (M.op (M.op (τ X0) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq649 (τ X0) X1
       have i₂ := eq416 X0 X0
       grind)
    | exact superpose eq416 eq649
    | exact resolve eq649 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq649 X0 X2
       have i₂ := eq649 X0 X1
       grind)
    | exact superpose eq649 eq649
    | exact resolve eq649 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : (M.op (k x x) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq649 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq649
    | (have j0 := eq649 x y
       grind)
    | exact resolve eq649 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X0
       have i₂ := eq649 X0 X1
       grind)
    | exact superpose eq649 eq187
    | exact resolve eq187 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 X0 X0 X2
       have i₂ := eq649 X0 X1
       grind)
    | exact superpose eq649 eq186
    | exact resolve eq186 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : x = (k (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq191 x
       have i₂ := eq659
       grind)
    | exact superpose eq659 eq191
    | exact resolve eq191 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq11 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : y ≠ (M.op x y) ∨ x = y ∨ (k y x) = (M.op x x) := by
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
  have eq775 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq756 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq777 : y ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq773
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq773
    | exact resolve eq773 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq794 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq775
    | (have j0 := eq775 X0 X1
       grind)
    | exact resolve eq775 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq1169 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq742
       grind)
    | exact superpose eq742 eq40
    | exact resolve eq40 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq1170 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1169
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1169
    | exact resolve eq1169 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1172 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq1170
    | exact resolve eq1170 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1172 eq743
    | exact resolve eq743 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq1210
       have r₂ := eq27
       grind)
    | exact resolve eq1210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1223 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1217 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1217 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1217
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1217
       grind)
    | exact resolve eq12 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1228 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1217 eq649
    | exact resolve eq649 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1234 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1224
  have eq1235 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1234
  have eq1236 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1223
  have eq1243 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq1228
    | exact resolve eq1228 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1245 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1235
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1235
    | exact resolve eq1235 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1246 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq1236
    | exact resolve eq1236 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1250 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1172 eq1245
    | exact resolve eq1245 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq1245
  have eq1252 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1250 eq181
    | exact resolve eq181 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1253 : (τ (σ (M.op x y))) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1250 eq115
    | exact resolve eq115 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1250 eq187
    | exact resolve eq187 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) X0) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1250 eq664
    | exact resolve eq664 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1263 : (σ y) = (M.op (M.op (k (σ y) (σ y)) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1262 x
       have i₂ := eq649 sF3 x
       grind)
    | exact superpose eq649 eq1262
    | exact resolve eq1262 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1264 : (σ y) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1258 x
       have i₂ := eq649 sF1 x
       grind)
    | exact superpose eq649 eq1258
    | exact resolve eq1258 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq1267 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq1253
    | exact resolve eq1253 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1253
  have eq1268 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1243 eq1263
    | exact resolve eq1263 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1275 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq183 y x
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq183
    | exact resolve eq183 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1276 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x y) X0) (M.op X1 y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq186 y X0 X1
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq186
    | exact resolve eq186 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1278 : ∀ X0 : G, y = (M.op (k (M.op x y) (M.op x y)) (M.op X0 y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq190 y x
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq190
    | exact resolve eq190 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1279 : y = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq191 y
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq191
    | exact resolve eq191 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1294 : (σ (M.op x y)) = (M.op (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1268 eq190
    | exact resolve eq190 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1268 eq649
    | exact resolve eq649 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1312 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1243 eq191
    | exact resolve eq191 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1315 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1243 eq11
    | (have j0 := eq11 (k (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq11 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1333 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1250 eq1315
    | exact resolve eq1315 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1337 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1250 eq1333
    | exact resolve eq1333 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1340 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1250 eq1337
    | exact resolve eq1337 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1634 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X0) = (M.op (k X0 X1) (M.op X2 (M.op (k X0 X0) X0))) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq184 X0 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq184
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1644 : ∀ X0 X1 X3 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (k X0 X0) X0) (M.op X3 (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq184 (M.op X0 X1) (M.op x (M.op (k X0 X0) X0)) X3
       have i₂ := eq184 X0 X1 x
       grind)
    | exact superpose eq184 eq184
    | exact resolve eq184 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1859 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ y = (M.op X0 (M.op x y)) ∨ (M.op y y) = (k (M.op X0 (M.op x y)) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1275 eq12
    | (have j0 := eq12 (M.op x y) X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1275 X0
       grind)
    | exact resolve eq12 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1877 : ∀ X0 : G, (k y y) = (k (M.op X0 (M.op x y)) y) ∨ (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ y = (M.op X0 (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1859 X0
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1859
    | (have j0 := eq1859 X0
       grind)
    | exact resolve eq1859 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq1882 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ (M.op x y) = (k (M.op X0 (M.op x y)) y) ∨ y = (M.op X0 (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1267 eq1877
    | (have j0 := eq1877 X0
       grind)
    | exact resolve eq1877 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq1949 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1246 eq107
    | exact resolve eq107 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1246
  have eq1952 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq29 eq1949
    | exact resolve eq1949 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq2181 : y = (k (k (M.op x y) y) (k (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1279
       have i₂ := eq11 sF0 y
       grind)
    | exact superpose eq11 eq1279
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq1279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2646 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq794 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq794
    | (have j0 := eq794 (σ X0) (σ X1)
       grind)
    | exact resolve eq794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2663 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2646 X0 X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq2646
    | (have j0 := eq2646 X0 X1
       grind)
    | exact resolve eq2646 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2667 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2663 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq2663
    | (have j0 := eq2663 X0 X1
       grind)
    | exact resolve eq2663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq2816 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1340 eq132
    | exact resolve eq132 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq1340
  have eq10878 : ∀ X0 : G, (σ y) = (M.op (σ (M.op (M.op x y) y)) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1279 eq560
    | exact resolve eq560 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10887 : ∀ X0 : G, (σ y) = (M.op (σ (k (M.op x y) y)) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2181 eq560
    | exact resolve eq560 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181
  have eq10948 : ∀ X0 : G, (σ y) = (M.op (σ (k (M.op x y) y)) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10887 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10887
    | (have j0 := eq10887 X0
       grind)
    | exact resolve eq10887 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10887
  have eq10951 : ∀ X0 : G, (σ y) = (M.op (σ (M.op (M.op x y) y)) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10878 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10878
    | (have j0 := eq10878 X0
       grind)
    | exact resolve eq10878 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10878
  have eq10961 : ∀ X0 : G, (σ y) = (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10948 X0
       have i₂ := eq40 sF0
       grind)
    | exact superpose eq40 eq10948
    | exact resolve eq10948 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10948
  have eq10969 : ∀ X0 : G, (σ y) = (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq10961
    | (have j0 := eq10961 X0
       grind)
    | exact resolve eq10961 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10961
  have eq11284 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ y) (σ (M.op (M.op x y) y))) (k (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10951 eq664
    | exact resolve eq664 eq10951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10951
  have eq11313 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ y) (σ (M.op (M.op x y) y))) (σ (k (M.op (M.op x y) y) (M.op (M.op x y) y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11284
       have i₂ := eq10 (M.op sF0 y) (M.op sF0 y)
       grind)
    | exact superpose eq10 eq11284
    | exact resolve eq11284 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11284
  have eq11321 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ y) (σ (M.op (M.op x y) y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1279 eq11313
    | exact resolve eq11313 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279 eq11313
  have eq11326 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ y) (σ (M.op (M.op x y) y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11321
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11321
    | exact resolve eq11321 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11321
  have eq11329 : (M.op (k (σ y) (σ y)) (σ y)) = (σ (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11326
       have i₂ := eq649 sF3 (σ (M.op sF0 y))
       grind)
    | exact superpose eq649 eq11326
    | exact resolve eq11326 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11326
  have eq11331 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1243 eq11329
    | exact resolve eq11329 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11329
  have eq11332 : (M.op (σ x) (σ y)) = (σ (k (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11331
       have i₂ := eq11 sF0 y
       grind)
    | exact superpose eq11 eq11331
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq11331 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11336 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq11331 eq15
    | exact resolve eq15 eq11331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11382 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11332
       have i₂ := eq40 sF0
       grind)
    | exact superpose eq40 eq11332
    | exact resolve eq11332 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11332
  have eq11385 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq11382
    | exact resolve eq11382 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11382
  have eq11417 : y = (M.op (k (M.op x y) (M.op x y)) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq11336 eq1278
    | exact resolve eq1278 eq11336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq11418 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11336 eq1276
    | exact resolve eq1276 eq11336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq11432 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq11418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11418
  have eq11433 : y = (M.op (k (M.op x y) (M.op x y)) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq11417
  have eq27324 : ∀ X0 : G, (M.op (k y y) y) = (M.op x (M.op X0 (M.op (k y y) y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1634 y x X0
       have i₂ := eq1952
       grind)
    | exact superpose eq1952 eq1634
    | (have j0 := eq1634 y x x
       grind)
    | exact resolve eq1634 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq27532 : ∀ X0 : G, (M.op (k y y) y) = (M.op x (M.op X0 (M.op (k y y) y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq27324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27324
  have eq27569 : ∀ X0 : G, y = (M.op x y) ∨ (M.op (k y y) y) = (M.op x (M.op X0 (M.op (k y y) y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq27532 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27532
    | (have j0 := eq27532 X0
       grind)
    | exact resolve eq27532 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27532
  have eq27612 : ∀ X0 : G, y = (M.op x y) ∨ (M.op (M.op x y) y) = (M.op x (M.op X0 (M.op (M.op x y) y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1267 eq27569
    | exact resolve eq27569 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27569
  have eq27629 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op X0 (τ (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq11336 eq27612
    | exact resolve eq27612 eq11336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11336 eq27612
  have eq27715 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq11433 eq27629
    | exact resolve eq27629 eq11433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11433
  have eq27736 : (M.op (k x x) x) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27629 eq649
    | exact resolve eq649 eq27629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27629
  have eq27752 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq27715
  have eq27763 : (M.op (M.op x y) x) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq27736
       have i₂ := eq659
       grind)
    | exact superpose eq659 eq27736
    | exact resolve eq27736 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq27736
  have eq27769 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq27752
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27752
    | exact resolve eq27752 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27752
  have eq28735 : ∀ X0 : G, (M.op (M.op (τ (M.op (σ x) (σ y))) X0) (τ (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) x) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq27763 eq655
    | exact resolve eq655 eq27763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq27763
  have eq28743 : (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) x) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq28735 x
       have i₂ := eq653 sF4 x
       grind)
    | exact superpose eq653 eq28735
    | exact resolve eq28735 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq28735
  have eq28752 : (M.op (τ (σ y)) (τ (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) x) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1312 eq28743
    | exact resolve eq28743 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312 eq28743
  have eq28759 : (M.op y (τ (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) x) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31 eq28752
    | exact resolve eq28752 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28752
  have eq28767 : y = (M.op y (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq11432 eq28759
    | exact resolve eq28759 eq11432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11432 eq28759
  have eq28773 : y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27769 eq28767
    | exact resolve eq28767 eq27769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27769 eq28767
  have eq28803 : (M.op y y) = (M.op (k y y) y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28773 eq649
    | exact resolve eq649 eq28773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28773
  have eq28833 : (k y y) = (M.op (k y y) y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq28803
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq28803
    | exact resolve eq28803 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28803
  have eq28856 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1267 eq28833
    | exact resolve eq28833 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267 eq28833
  have eq28904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28856 eq11331
    | exact resolve eq11331 eq28856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28856
  have eq29012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28904
  have eq29081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq29012
    | exact resolve eq29012 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29012
  have eq29113 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq29081
       have r₂ := eq27
       grind)
    | exact resolve eq29081 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29081
  have eq29123 : x = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq29113
       grind)
    | exact superpose eq29113 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq29113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29135 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq665 y x X0
       have i₂ := eq29113
       grind)
    | exact superpose eq29113 eq665
    | exact resolve eq665 eq29113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29138 : x = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29123
  have eq29140 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq29135 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29135
    | (have j0 := eq29135 X0
       grind)
    | exact resolve eq29135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29135
  have eq29148 : y = (M.op x y) ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29138
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29138
    | exact resolve eq29138 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29138
  have eq29149 : x = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29148
  have eq29156 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq29149
       grind)
    | exact superpose eq29149 eq36
    | exact resolve eq36 eq29149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq29149
  have eq29172 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29156
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29156
    | exact resolve eq29156 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29156
  have eq29179 : ∀ X0 : G, (M.op (k (σ y) (σ y)) (σ y)) = (M.op (σ x) (M.op X0 (M.op (k (σ y) (σ y)) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29172 eq1634
    | (have j0 := eq1634 (σ y) (σ x) x
       grind)
    | exact resolve eq1634 eq29172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634
  have eq29181 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29172 eq794
    | (have j0 := eq794 (σ y) (σ x)
       grind)
    | (have r₁ := eq794 (σ y) (σ x)
       have r₂ := eq29172
       grind)
    | exact resolve eq794 eq29172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq29172
  have eq29182 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29181
  have eq29183 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29182
  have eq29185 : ∀ X0 : G, (M.op (k (σ y) (σ y)) (σ y)) = (M.op (σ x) (M.op X0 (M.op (k (σ y) (σ y)) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29179 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29179
  have eq29188 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq29183
    | exact resolve eq29183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29183
  have eq29189 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq29188
  have eq29192 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (k (σ y) (σ y)) (σ y)) = (M.op (σ x) (M.op X0 (M.op (k (σ y) (σ y)) (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq29185
    | (have j0 := eq29185 X0
       grind)
    | exact resolve eq29185 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29185
  have eq29193 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (k (σ y) (σ y)) (σ y)) = (M.op (σ x) (M.op X0 (M.op (k (σ y) (σ y)) (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq29192 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29192
  have eq29197 : ∀ X0 : G, (M.op (k (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op X0 (M.op (k (σ x) (σ y)) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29189 eq29193
    | exact resolve eq29193 eq29189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29193
  have eq29249 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29140 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29140
    | (have j0 := eq29140 x
       grind)
    | exact resolve eq29140 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29140
  have eq29336 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29249
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq29249
    | exact resolve eq29249 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29249
  have eq29742 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29336 eq41
    | exact resolve eq41 eq29336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29749 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29336 eq560
    | exact resolve eq560 eq29336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29336
  have eq29772 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq29749 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29749
    | (have j0 := eq29749 X0
       grind)
    | exact resolve eq29749 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29749
  have eq29775 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq29742
    | exact resolve eq29742 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29742
  have eq29779 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq29772
    | (have j0 := eq29772 X0
       grind)
    | exact resolve eq29772 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29772
  have eq29780 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29775
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29775
    | exact resolve eq29775 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29775
  have eq29805 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29780 eq187
    | exact resolve eq187 eq29780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29780
  have eq29837 : (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29805 x
       have i₂ := eq649 sF3 x
       grind)
    | exact superpose eq649 eq29805
    | exact resolve eq29805 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29805
  have eq29842 : (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29189 eq29837
    | exact resolve eq29837 eq29189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29189 eq29837
  have eq39016 : ∀ X1 : G, (M.op (k (σ y) (σ y)) (σ y)) = (M.op (M.op (k (k (σ (M.op x y)) (σ y)) (k (σ (M.op x y)) (σ y))) (k (σ (M.op x y)) (σ y))) (M.op X1 (M.op (k (σ y) (σ y)) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq10969 eq1644
    | exact resolve eq1644 eq10969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10969
  have eq39326 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (k (k (σ (M.op x y)) (σ y)) (k (σ (M.op x y)) (σ y))) (k (σ (M.op x y)) (σ y))) (M.op X1 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq1243 eq39016
    | exact resolve eq39016 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39016
  have eq39722 : ∀ X1 : G, (σ y) = (M.op (M.op (k (k (σ (M.op x y)) (σ y)) (k (σ (M.op x y)) (σ y))) (k (σ (M.op x y)) (σ y))) (M.op X1 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq29113 eq39326
    | exact resolve eq39326 eq29113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39326
  have eq40035 : ∀ X1 : G, (σ y) = (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op X1 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq11385 eq39722
    | exact resolve eq39722 eq11385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11385 eq39722
  have eq40245 : ∀ X1 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X1 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq1295 eq40035
    | exact resolve eq40035 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295 eq40035
  have eq40393 : ∀ X1 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op X1 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq29113 eq40245
    | exact resolve eq40245 eq29113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40245
  have eq40476 : ∀ X1 : G, (σ y) = (M.op (k (σ y) (σ y)) (M.op X1 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq40393 X1
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq40393
    | exact resolve eq40393 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40393
  have eq40516 : ∀ X1 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X1 (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq1250 eq40476
    | exact resolve eq40476 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40476
  have eq57181 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40516 eq1252
    | exact resolve eq1252 eq40516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252 eq40516
  have eq57246 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq57181
  have eq57300 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29113 eq57246
    | exact resolve eq57246 eq29113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57246
  have eq57333 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57300
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq57300
    | exact resolve eq57300 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57300
  have eq57342 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1250 eq57333
    | exact resolve eq57333 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57333
  have eq57383 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57342 eq1882
    | (have r₁ := eq1882 y
       have r₂ := eq57342
       grind)
    | exact resolve eq1882 eq57342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882 eq57342
  have eq57427 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq57383
  have eq57428 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq57427
  have eq57555 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq57428 eq2816
    | exact resolve eq2816 eq57428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816 eq57428
  have eq57585 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq57555
  have eq57597 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29113 eq57585
    | exact resolve eq57585 eq29113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57585
  have eq57604 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq57597
    | exact resolve eq57597 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57597
  have eq57605 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq57604
  have eq57719 : ∀ X0 : G, (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (M.op (k (σ y) (σ y)) (σ y)) (M.op X0 (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq57605 eq1644
    | exact resolve eq1644 eq57605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq57775 : ∀ X0 : G, (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1243 eq57719
    | exact resolve eq57719 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243 eq57719
  have eq57797 : ∀ X0 : G, (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ y) (M.op X0 (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29113 eq57775
    | exact resolve eq57775 eq29113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29113 eq57775
  have eq57805 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1264 eq57797
    | exact resolve eq57797 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq57797
  have eq58670 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1294 eq57805
    | exact resolve eq57805 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq57805
  have eq58783 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq58670
  have eq58951 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq58783 eq57605
    | exact resolve eq57605 eq58783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57605 eq58783
  have eq59020 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq58951
  have eq59067 : x ≠ x ∨ x = y ∨ (k x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq59020
       grind)
    | exact superpose eq59020 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq59020
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq59020
       grind)
    | exact resolve eq12 eq59020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59073 : (M.op x y) = (M.op (k y y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq649 y x
       have i₂ := eq59020
       grind)
    | exact superpose eq59020 eq649
    | exact resolve eq649 eq59020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59076 : y = (M.op (M.op x y) (k y y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq664 y x
       have i₂ := eq59020
       grind)
    | exact superpose eq59020 eq664
    | exact resolve eq664 eq59020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq59078 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq665 y x X0
       have i₂ := eq59020
       grind)
    | exact superpose eq59020 eq665
    | exact resolve eq665 eq59020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59020
  have eq59084 : x ≠ x ∨ x = y ∨ (k x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59067
  have eq59085 : x = y ∨ (k x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59084
  have eq59091 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq59078 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59078
    | (have j0 := eq59078 X0
       grind)
    | exact resolve eq59078 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59078
  have eq59093 : y = (M.op (M.op x y) (k y y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59076
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59076
    | exact resolve eq59076 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59076
  have eq59096 : (M.op x y) = (M.op (k y y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59073
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59073
    | exact resolve eq59073 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59073
  have eq59098 : (k x y) = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq59085
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq59085
    | exact resolve eq59085 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59085
  have eq62159 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59091 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59091
    | (have j0 := eq59091 x
       grind)
    | exact resolve eq59091 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59091
  have eq62268 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62159
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq62159
    | exact resolve eq62159 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62159
  have eq62295 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62268 eq41
    | exact resolve eq41 eq62268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62302 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq62268 eq560
    | exact resolve eq560 eq62268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq62268
  have eq62336 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq62302 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62302
    | (have j0 := eq62302 X0
       grind)
    | exact resolve eq62302 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62302
  have eq62339 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq62295
    | exact resolve eq62295 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62295
  have eq62346 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq62336
    | (have j0 := eq62336 X0
       grind)
    | exact resolve eq62336 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62336
  have eq62347 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62339
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62339
    | exact resolve eq62339 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62339
  have eq62373 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (M.op X1 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq62347 eq186
    | exact resolve eq186 eq62347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq62374 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq62347 eq187
    | exact resolve eq187 eq62347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq62347
  have eq62414 : (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62374 x
       have i₂ := eq649 sF3 x
       grind)
    | exact superpose eq649 eq62374
    | exact resolve eq62374 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62374
  have eq62626 : (σ (k x y)) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq59098
       grind)
    | exact superpose eq59098 eq40
    | exact resolve eq40 eq59098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59098
  have eq62666 : (σ (k x y)) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq62626
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62626
    | exact resolve eq62626 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62626
  have eq62672 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq62666
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq62666
    | exact resolve eq62666 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq62666
  have eq62677 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq62672
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62672
    | exact resolve eq62672 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62672
  have eq62936 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq62346
    | (have j0 := eq62346 (σ x)
       grind)
    | exact resolve eq62346 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62346
  have eq63375 : (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq62677 eq62414
    | exact resolve eq62414 eq62677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63422 : (σ y) = (M.op (k (k (σ y) (σ y)) (k (σ y) (σ y))) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62414 eq190
    | exact resolve eq190 eq62414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62414
  have eq63461 : (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq63375
  have eq63479 : (σ y) = (M.op (k (k (σ x) (σ y)) (k (σ x) (σ y))) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62677 eq63422
    | exact resolve eq63422 eq62677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62677 eq63422
  have eq63512 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq743 eq63461
    | exact resolve eq63461 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63461
  have eq63601 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq63512
  have eq67106 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq63601 eq62373
    | exact resolve eq62373 eq63601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62373 eq63601
  have eq67133 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq67106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67106
  have eq71388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63479 eq67133
    | exact resolve eq67133 eq63479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63479 eq67133
  have eq71454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq71388
  have eq71484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq71454
    | exact resolve eq71454 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71454
  have eq71495 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq71484
       have r₂ := eq27
       grind)
    | exact resolve eq71484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71484
  have eq71555 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq71495 eq665
    | exact resolve eq665 eq71495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71495
  have eq71602 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq62936 eq71555
    | exact resolve eq71555 eq62936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71555
  have eq71672 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62936 eq71602
    | exact resolve eq71602 eq62936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62936 eq71602
  have eq71785 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq71672
  have eq71834 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq71785
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq71785
    | exact resolve eq71785 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71785
  have eq71866 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq71834 eq115
    | exact resolve eq115 eq71834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71834
  have eq72077 : y = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59093
       have i₂ := eq71866
       grind)
    | exact superpose eq71866 eq59093
    | exact resolve eq59093 eq71866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59093
  have eq72078 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59096
       have i₂ := eq71866
       grind)
    | exact superpose eq71866 eq59096
    | exact resolve eq59096 eq71866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59096
  have eq72091 : y = (k (M.op (τ (M.op (σ x) (σ y))) y) (M.op (τ (M.op (σ x) (σ y))) y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq191 y
       have i₂ := eq71866
       grind)
    | exact superpose eq71866 eq191
    | exact resolve eq191 eq71866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq71866
  have eq72111 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq72078
  have eq72112 : y = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq72077
  have eq72861 : (τ (M.op (σ x) (σ y))) = (M.op (k (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq72112 eq190
    | exact resolve eq190 eq72112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq72112
  have eq72905 : (τ (M.op (σ x) (σ y))) = (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq72861
       have i₂ := eq416 sF4 sF4
       grind)
    | exact superpose eq416 eq72861
    | exact resolve eq72861 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72861
  have eq72916 : (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq72905
       have i₂ := eq416 (k sF4 sF4) (k sF4 sF4)
       grind)
    | exact superpose eq416 eq72905
    | exact resolve eq72905 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq72905
  have eq93000 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29779 eq29197
    | exact resolve eq29197 eq29779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29197 eq29779
  have eq93055 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq93000
  have eq93111 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq93055
    | exact resolve eq93055 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93055
  have eq93150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29842 eq93111
    | exact resolve eq93111 eq29842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29842 eq93111
  have eq93184 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq93150
       have r₂ := eq27
       grind)
    | exact resolve eq93150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93150
  have eq93211 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93184 eq27
    | exact resolve eq27 eq93184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93453 : y = (k (M.op (τ (σ y)) y) (M.op (τ (σ y)) y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93184 eq72091
    | exact resolve eq72091 eq93184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72091
  have eq93454 : (M.op x y) = (M.op (τ (σ y)) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93184 eq72111
    | exact resolve eq72111 eq93184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72111
  have eq93463 : (τ (σ y)) = (M.op (τ (k (k (σ y) (σ y)) (k (σ y) (σ y)))) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93184 eq72916
    | exact resolve eq72916 eq93184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72916 eq93184
  have eq93492 : (τ (σ y)) = (M.op (τ (k (k (σ y) (σ y)) (k (σ y) (σ y)))) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq93463
  have eq93501 : (M.op x y) = (M.op (τ (σ y)) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq93454
  have eq93502 : y = (k (M.op (τ (σ y)) y) (M.op (τ (σ y)) y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq93453
  have eq93743 : (τ (σ y)) = (M.op (k (k y y) (τ (k (σ y) (σ y)))) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq519 eq93492
    | exact resolve eq93492 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq93492
  have eq93751 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq93501
    | exact resolve eq93501 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93501
  have eq93752 : y = (k (M.op y y) (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq93502
    | exact resolve eq93502 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93502
  have eq93906 : (τ (σ y)) = (M.op (k (k y y) (τ (k (σ y) (σ y)))) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq93743
       have r₂ := eq93211
       grind)
    | exact resolve eq93743 eq93211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93743
  have eq93914 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq93751
       have r₂ := eq93211
       grind)
    | exact resolve eq93751 eq93211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93751
  have eq93915 : y = (k (M.op y y) (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq93752
       have r₂ := eq93211
       grind)
    | exact resolve eq93752 eq93211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93211 eq93752
  have eq94021 : (τ (σ y)) = (M.op (k (k y y) (k y y)) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq115 eq93906
    | exact resolve eq93906 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq93906
  have eq94025 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq93914
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq93914
    | exact resolve eq93914 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93914
  have eq94026 : y = (k (k y y) (k y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93915
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq93915
    | exact resolve eq93915 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93915
  have eq94065 : y = (M.op (k (k y y) (k y y)) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq94021
    | exact resolve eq94021 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94021
  have eq94066 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq94025 eq94026
    | exact resolve eq94026 eq94025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94026
  have eq94069 : y = (M.op (k (M.op x y) (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq94025 eq94065
    | exact resolve eq94065 eq94025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94065
  have eq94071 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq94066 eq94069
    | exact resolve eq94069 eq94066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94066 eq94069
  have eq94072 : y = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94071
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq94071
    | exact resolve eq94071 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94071
  have eq94073 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq94025 eq94072
    | exact resolve eq94072 eq94025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94025 eq94072
  have eq94074 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq94073
  have eq94076 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq94074 eq31
    | exact resolve eq31 eq94074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94093 : (k y x) = (τ (k (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq94074 eq114
    | exact resolve eq114 eq94074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq94117 : (k x x) = (k y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq97 eq94093
    | exact resolve eq94093 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq94093
  have eq94134 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq94076
    | exact resolve eq94076 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94076
  have eq94135 : y = (M.op x y) ∨ x = y := by grind
  clear eq94134
  have eq94137 : (k x x) = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq94117
       have r₂ := eq777
       grind)
    | exact resolve eq94117 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq94117
  have eq94138 : (k x x) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq94135 eq94137
    | exact resolve eq94137 eq94135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94137
  have eq94139 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq94135
       grind)
    | exact superpose eq94135 eq18
    | exact resolve eq18 eq94135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94140 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq94135
       grind)
    | exact superpose eq94135 eq24
    | exact resolve eq24 eq94135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94217 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11331
       have i₂ := eq94135
       grind)
    | exact superpose eq94135 eq11331
    | exact resolve eq11331 eq94135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11331
  have eq94306 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq94135
  have eq94399 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have r₁ := eq94217
       have r₂ := eq94306
       grind)
    | exact resolve eq94217 eq94306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94217
  have eq94467 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq94140
    | exact resolve eq94140 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94140
  have eq94511 : (M.op (σ x) (σ y)) = (σ (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq94399
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq94399
    | exact resolve eq94399 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94399
  have eq94570 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq41 eq94511
    | exact resolve eq94511 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94511
  have eq94620 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq20 eq94570
    | exact resolve eq94570 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94570
  have eq94656 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq94467 eq94620
    | exact resolve eq94620 eq94467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94620
  have eq102970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq94656 eq1250
    | exact resolve eq1250 eq94656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq94656
  have eq103012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op (M.op x y) x) := by grind
  clear eq102970
  have eq103041 : (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq103012
       have r₂ := eq27
       grind)
    | exact resolve eq103012 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103012
  have eq103061 : (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq94074 eq103041
    | exact resolve eq103041 eq94074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94074 eq103041
  have eq103062 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq103061
  have eq103076 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq103062 eq681
    | exact resolve eq681 eq103062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq103133 : x ≠ x ∨ x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq103062 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq103062
       grind)
    | exact resolve eq12 eq103062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103144 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op x y)) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq103062 eq665
    | exact resolve eq665 eq103062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq103062
  have eq103153 : x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq103133
  have eq103206 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq94139 eq103144
    | exact resolve eq103144 eq94139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103144
  have eq103216 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq103153
       have r₂ := eq94306
       grind)
    | exact resolve eq103153 eq94306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94306 eq103153
  have eq103264 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq103216
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq103216
    | exact resolve eq103216 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103216
  have eq103325 : x = (k (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94138
       have i₂ := eq103076
       grind)
    | exact superpose eq103076 eq94138
    | exact resolve eq94138 eq103076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94138 eq103076
  have eq103359 : x = (k (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq103325
  have eq103639 : (σ x) ≠ (σ x) ∨ (σ (k x (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq103359 eq2667
    | (have j0 := eq2667 (M.op x y) x
       grind)
    | exact resolve eq2667 eq103359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667 eq103359
  have eq103644 : (σ (k x (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq103639
  have eq103659 : (σ (k x (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41 eq103644
    | exact resolve eq103644 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103644
  have eq103673 : (σ (k x (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq103659
    | exact resolve eq103659 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103659
  have eq103684 : (k (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41 eq103673
    | exact resolve eq103673 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103673
  have eq103691 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103684
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq103684
    | exact resolve eq103684 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103684
  have eq103696 : (σ x) = (σ (M.op x y)) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq103691
    | exact resolve eq103691 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103691
  have eq103701 : (σ (M.op x y)) = (σ x) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103696
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq103696
    | exact resolve eq103696 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103696
  have eq103706 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq103701
    | exact resolve eq103701 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103701
  have eq103711 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103706
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq103706
    | exact resolve eq103706 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103706
  have eq103712 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq94467 eq103711
    | exact resolve eq103711 eq94467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103711
  have eq103713 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq103712
    | exact resolve eq103712 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103712
  have eq103714 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq94467 eq103713
    | exact resolve eq103713 eq94467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103713
  have eq103715 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ x = y := by grind
  clear eq103714
  have eq103716 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq94467 eq103715
    | exact resolve eq103715 eq94467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103715
  have eq104365 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq94139 eq103206
    | exact resolve eq103206 eq94139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94139 eq103206
  have eq104454 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq104365
  have eq104522 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq104454
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq104454
    | exact resolve eq104454 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104454
  have eq104612 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq104522 eq41
    | exact resolve eq41 eq104522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104522
  have eq104680 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq104612
    | exact resolve eq104612 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104612
  have eq104707 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq94467 eq104680
    | exact resolve eq104680 eq94467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104680
  have eq105714 : (k (σ x) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq103264 eq35
    | exact resolve eq35 eq103264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq103264
  have eq105736 : (k (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq41 eq105714
    | exact resolve eq105714 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq105714
  have eq105745 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq105736
    | exact resolve eq105736 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105736
  have eq105754 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq94467 eq105745
    | exact resolve eq105745 eq94467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105745
  have eq105763 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq104707 eq105754
    | exact resolve eq105754 eq104707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105754
  have eq106481 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq105763 eq743
    | exact resolve eq743 eq105763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq106635 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq106481
  have eq107726 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq106635 eq649
    | exact resolve eq649 eq106635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq106635
  have eq107780 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq107726
    | exact resolve eq107726 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107726
  have eq107800 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq103716 eq107780
    | exact resolve eq107780 eq103716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103716 eq107780
  have eq107816 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq105763 eq107800
    | exact resolve eq107800 eq105763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105763 eq107800
  have eq107827 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq107816
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107816
    | exact resolve eq107816 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107816
  have eq107834 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq104707 eq107827
    | exact resolve eq107827 eq104707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104707 eq107827
  have eq107835 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq107834
  have eq107843 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq107835 eq27
    | exact resolve eq27 eq107835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107835
  have eq108533 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq107843
       have r₂ := eq94467
       grind)
    | exact resolve eq107843 eq94467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94467 eq107843
  have eq108637 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq108533 eq31
    | exact resolve eq31 eq108533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq108533
  have eq108706 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq108637
    | exact resolve eq108637 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq108637
  have eq108707 : x = y := by grind
  clear eq108706
  have eq108738 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq108707
       grind)
    | exact superpose eq108707 eq18
    | exact resolve eq18 eq108707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq108739 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq108707
       grind)
    | exact superpose eq108707 eq24
    | exact resolve eq24 eq108707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq108707
  have eq108752 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq108739
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108739
    | exact resolve eq108739 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108739
  have eq108753 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq108738
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq108738
    | exact resolve eq108738 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108738
  have eq108754 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq108752 eq26
    | exact resolve eq26 eq108752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq108752
  have eq108821 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq108754
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq108754
    | exact resolve eq108754 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq108754
  have eq108844 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq108753
       grind)
    | exact superpose eq108753 eq39
    | exact resolve eq39 eq108753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq108753
  have eq108870 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq108844
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108844
    | exact resolve eq108844 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq108844
  have eq108876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108821 eq108870
    | exact resolve eq108870 eq108821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108821 eq108870
  have eq108878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq108876
    | exact resolve eq108876 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq108876
  have eq108880 : False := by grind
  exact eq108880

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq36 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq182 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq55
  have eq219 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq182 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq3299 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq3315 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3299 X0 X1
       have j1 := eq57 X0 X1
       grind)
    | (have r₁ := eq3299 X0 X1
       have r₂ := eq57 X0 X1
       grind)
    | (have r₁ := eq3299 X1 X1
       have r₂ := eq57 X1 X1
       grind)
    | exact resolve eq3299 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq3299
  have eq3542 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3315 (σ X0) (σ X1)
       grind)
    | exact superpose eq3315 eq15
    | exact resolve eq15 eq3315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3553 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3542 X0 X1
       have i₂ := eq3315 X0 X1
       grind)
    | exact superpose eq3315 eq3542
    | exact resolve eq3542 eq3315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315 eq3542
  have eq3561 : False := by grind
  exact eq3561

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pyy_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq103 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq115 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq103 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq103 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq103 X0 X1
       have r₂ := eq12 (k X0 X1) X1
       grind)
    | exact resolve eq103 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq181 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq24 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq24 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq235 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 X1) = X2 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1
       have i₂ := eq181 X0 X2
       grind)
    | (have i₁ := eq14 X2 X1
       have i₂ := eq181 X2 X0
       grind)
    | exact superpose eq181 eq14
    | (have j0 := eq14 X2 X1
       grind)
    | exact resolve eq14 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq246 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq235 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq235 X1 X1 X2
       have r₂ := eq12 (M.op X1 X2) X1
       grind)
    | (have r₁ := eq235 X0 X1 X1
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq235 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq235 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq340 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq343 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq340 X0 X1
       have j1 := eq246 X0 X1 X0
       grind)
    | (have r₁ := eq340 x X1
       have r₂ := eq246 X1 X1 x
       grind)
    | (have r₁ := eq340 X0 X0
       have r₂ := eq246 X0 X0 X0
       grind)
    | exact resolve eq340 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq340
  have eq368 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq343 (σ X1) (σ X0)
       grind)
    | exact superpose eq343 eq15
    | exact resolve eq15 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq343 X1 X0
       grind)
    | exact superpose eq343 eq368
    | exact resolve eq368 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq368
  have eq2694 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq373 x y
       grind)
    | exact superpose eq373 eq16
    | (have r₁ := eq16
       have r₂ := eq373 x y
       grind)
    | exact resolve eq16 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq2751 : False := by grind
  exact eq2751
