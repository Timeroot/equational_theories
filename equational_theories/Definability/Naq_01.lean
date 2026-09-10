import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq81 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq87
    | (have j0 := eq87 X0 (σ X1)
       grind)
    | exact resolve eq87 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
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
  clear eq44
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq119 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq130 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq119 eq16
    | exact resolve eq16 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq216 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq87 (τ X0) X1
       grind)
    | exact superpose eq87 eq34
    | (have j1 := eq87 X0 X1
       grind)
    | exact resolve eq34 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq38
  have eq353 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 X0 x X3
       have i₂ := eq53 X0 x X1
       grind)
    | (have i₁ := eq53 x x x
       have i₂ := eq53 x X1 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X1)) X2 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq353
    | exact resolve eq353 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq411 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq390 X0 x
       have i₂ := eq53 X0 x X1
       grind)
    | (have i₁ := eq390 x x
       have i₂ := eq53 x X1 x
       grind)
    | exact superpose eq53 eq390
    | exact resolve eq390 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq91 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq111 eq87
    | (have j0 := eq87 x (σ y)
       grind)
    | exact resolve eq87 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq807
    | exact resolve eq807 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq811 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq808
       have r₂ := eq27
       grind)
    | exact resolve eq808 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq817 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq811 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq811
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq811
       grind)
    | exact resolve eq13 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq1172 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq827 eq81
    | exact resolve eq81 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq827
  have eq1312 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq811 eq1172
    | exact resolve eq1172 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq1172
  have eq1325 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq1312
  have eq1327 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1325
    | exact resolve eq1325 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1325
  have eq1330 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq87 y y
       have i₂ := eq1327
       grind)
    | exact superpose eq1327 eq87
    | (have j0 := eq87 x y
       grind)
    | exact resolve eq87 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1331 : y = (M.op y y) := by grind
  clear eq1330
  have eq1335 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1331
       grind)
    | exact resolve eq13 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1336 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 y
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq14
    | exact resolve eq14 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1337 : x = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq50
    | exact resolve eq50 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1339 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 y
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq53
    | exact resolve eq53 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq196 y
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq196
    | exact resolve eq196 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1341 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq198 y
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq198
    | exact resolve eq198 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1342 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 y X1
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq360
    | exact resolve eq360 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1346 : ∀ X0 : G, (M.op (M.op X0 y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq411 X0 y
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq411
    | exact resolve eq411 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq1352 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq1335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1359 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1340
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1340
    | exact resolve eq1340 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1361 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq1359 eq370
    | exact resolve eq370 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1419 : x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1359 eq1337
    | exact resolve eq1337 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1485 : ∀ X0 : G, (k (τ y) X0) = (τ (M.op y (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq285 y X0
       have i₂ := eq1352 (σ X0)
       grind)
    | exact superpose eq1352 eq285
    | exact resolve eq285 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq1491 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq1352 y
       grind)
    | exact superpose eq1352 eq70
    | exact resolve eq70 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1352
  have eq1495 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1491
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq1491
    | exact resolve eq1491 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1497 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1495
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1495
    | exact resolve eq1495 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1495
  have eq1544 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1497 eq87
    | (have j0 := eq87 x (σ y)
       grind)
    | exact resolve eq87 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1545 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1544
  have eq1559 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1545 eq198
    | exact resolve eq198 eq1545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq1545
  have eq1578 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1341 eq1559
    | exact resolve eq1559 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq1582 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq26 eq1578
    | exact resolve eq1578 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1578
  have eq1603 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1582 eq1346
    | exact resolve eq1346 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq2826 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (τ X0) X2))) = (σ (M.op (τ X0) (M.op X1 X1))) ∨ (M.op (τ X0) X2) = (M.op (M.op (τ X0) X2) (M.op (τ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq282 X0 (M.op (τ X0) X2)
       have i₂ := eq53 (τ X0) X2 X1
       grind)
    | (have i₁ := eq282 X0 (M.op X2 X2)
       have i₂ := eq53 (τ X0) X1 X2
       grind)
    | exact superpose eq53 eq282
    | (have j0 := eq282 X0 (M.op (τ X0) X2)
       grind)
    | exact resolve eq282 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2827 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (M.op X1 X1))) = (k X0 (σ (M.op X2 X2))) ∨ (M.op X2 X2) = (M.op (M.op X2 X2) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq282 X0 (M.op X2 X2)
       have i₂ := eq360 (τ X0) X2 X1
       grind)
    | (have i₁ := eq282 X0 (M.op X2 X2)
       have i₂ := eq360 (τ X0) X1 X2
       grind)
    | exact superpose eq360 eq282
    | (have j0 := eq282 X0 (M.op X2 X2)
       grind)
    | exact resolve eq282 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq3552 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq527 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq527
    | (have j0 := eq527 (τ X0)
       grind)
    | exact resolve eq527 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3561 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3552 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3552
    | (have j0 := eq3552 X0
       grind)
    | exact resolve eq3552 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552
  have eq3570 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3561 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3561
    | (have j0 := eq3561 X0
       grind)
    | exact resolve eq3561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3561
  have eq4622 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1336 X0 x
       have i₂ := eq1339 X0 x
       grind)
    | exact superpose eq1339 eq1336
    | exact resolve eq1336 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq7847 : ∀ X0 : G, (k (τ y) (τ X0)) = (τ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1485 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1485
    | exact resolve eq1485 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485
  have eq96647 : (τ y) ≠ (τ (M.op y y)) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq3570 (τ y)
       have i₂ := eq7847 y
       grind)
    | exact superpose eq7847 eq3570
    | (have j0 := eq3570 (τ y)
       grind)
    | exact resolve eq3570 eq7847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7847
  have eq96669 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq96647
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq96647
    | exact resolve eq96647 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331 eq96647
  have eq96670 : (τ y) = (M.op (τ y) (τ y)) := by grind
  clear eq96669
  have eq96672 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (M.op X0 X0) = X0 ∨ (k X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (τ y)
       have i₂ := eq96670
       grind)
    | exact superpose eq96670 eq12
    | (have j0 := eq12 X0 (τ y)
       grind)
    | (have r₁ := eq12 X0 (τ y)
       have r₂ := eq96670
       grind)
    | exact resolve eq12 eq96670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96670
  have eq96713 : ∀ X0 : G, (k X0 (τ y)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq96672 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96672
  have eq99837 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ y))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ y)
       have i₂ := eq96713 (τ X0)
       grind)
    | exact superpose eq96713 eq34
    | (have j1 := eq96713 (τ X0)
       grind)
    | exact resolve eq34 eq96713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq96713
  have eq100047 : ∀ X0 : G, (σ (τ X0)) = (k X0 y) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq99837 X0
       have i₂ := eq15 y
       grind)
    | exact superpose eq15 eq99837
    | (have j0 := eq99837 X0
       grind)
    | exact resolve eq99837 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99837
  have eq100199 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq100047 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq100047
    | (have j0 := eq100047 X0
       grind)
    | exact resolve eq100047 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100047
  have eq226792 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (τ X0)) ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1342 X1 (τ X0)
       have i₂ := eq100199 X0
       grind)
    | exact superpose eq100199 eq1342
    | (have j1 := eq100199 X0
       grind)
    | exact resolve eq1342 eq100199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300683 : ∀ X0 : G, (τ X0) = (M.op (τ X0) y) ∨ (k X0 y) = X0 ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq100199 X0
       have i₂ := eq226792 X0 (τ X0)
       grind)
    | exact superpose eq226792 eq100199
    | (have j0 := eq100199 X0
       have j1 := eq226792 X0 x
       grind)
    | exact resolve eq100199 eq226792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100199 eq226792
  have eq300818 : ∀ X0 : G, (τ X0) = (M.op (τ X0) y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq300683 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300683
  have eq304546 : ∀ X0 : G, (σ X0) = (k (σ X0) y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq300818 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq300818
    | (have j0 := eq300818 (σ X0)
       grind)
    | exact resolve eq300818 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300818
  have eq319317 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq319 X0 y
       have i₂ := eq304546 X0
       grind)
    | exact superpose eq304546 eq319
    | (have j1 := eq304546 X0
       grind)
    | exact resolve eq319 eq304546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq304546
  have eq319414 : ∀ X0 : G, (k X0 (τ y)) = X0 ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq319317 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq319317
    | (have j0 := eq319317 X0
       grind)
    | exact resolve eq319317 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319317
  have eq319561 : x = (τ (k (σ x) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq216 y
       have i₂ := eq319414 x
       grind)
    | exact superpose eq319414 eq216
    | (have j1 := eq319414 x
       grind)
    | exact resolve eq216 eq319414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq319414
  have eq320197 : x = (τ (k (σ x) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq319561
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq319561
    | exact resolve eq319561 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319561
  have eq321827 : (σ (k x x)) = (k (σ x) (k (σ x) y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq320197 eq42
    | exact resolve eq42 eq320197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq322171 : (k (σ x) (σ x)) = (k (σ x) (k (σ x) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq321827
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq321827
    | exact resolve eq321827 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq321827
  have eq451402 : ∀ X0 X2 : G, (k X0 (σ (M.op X2 X2))) = (σ (M.op (τ X0) y)) ∨ (M.op X2 X2) = (M.op (M.op X2 X2) (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq2827 X0 x X2
       have i₂ := eq1342 (τ X0) x
       grind)
    | exact superpose eq1342 eq2827
    | (have j0 := eq2827 X0 x X2
       grind)
    | exact resolve eq2827 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2827
  have eq451403 : ∀ X0 X2 : G, (k X0 (σ (M.op X2 X2))) = (σ (M.op (τ X0) y)) ∨ (M.op X2 X2) = (M.op (M.op X2 X2) y) := by
    intro X0 X2
    first
    | (have i₁ := eq451402 X0 X2
       have i₂ := eq1342 (M.op X2 X2) X2
       grind)
    | exact superpose eq1342 eq451402
    | (have j0 := eq451402 X0 X2
       grind)
    | exact resolve eq451402 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451402
  have eq452728 : ∀ X0 : G, (σ (M.op (τ (σ (M.op x y))) y)) = (σ (k (M.op x y) (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op x x)
       have i₂ := eq451403 sF1 x
       grind)
    | exact superpose eq451403 eq37
    | (have j1 := eq451403 X0 X0
       grind)
    | exact resolve eq37 eq451403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451403
  have eq453203 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (σ (k (M.op x y) (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | exact superpose eq30 eq452728
    | (have j0 := eq452728 X0
       grind)
    | exact resolve eq452728 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452728
  have eq453412 : ∀ X0 : G, (σ x) = (σ (k (M.op x y) (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | exact superpose eq1419 eq453203
    | (have j0 := eq453203 X0
       grind)
    | exact resolve eq453203 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453203
  have eq453519 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) y) ∨ (σ x) = (σ (k (M.op x y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq453412 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq453412
    | (have j0 := eq453412 X0
       grind)
    | exact resolve eq453412 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453412
  have eq530102 : ∀ X0 X2 : G, (M.op (τ X0) X2) = (M.op (M.op (τ X0) X2) (M.op (τ X0) X2)) ∨ (k X0 (σ (M.op (τ X0) X2))) = (σ (M.op (τ X0) y)) := by
    intro X0 X2
    first
    | (have i₁ := eq2826 X0 x X2
       have i₂ := eq1342 (τ X0) x
       grind)
    | exact superpose eq1342 eq2826
    | (have j0 := eq2826 X0 x X2
       grind)
    | exact resolve eq2826 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq530448 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) ∨ (σ (M.op (M.op x y) y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq30 eq530102
    | exact resolve eq530102 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq530102
  have eq530641 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (σ (k (M.op x y) (M.op (M.op x y) X0))) ∨ (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq37 eq530448
    | (have j0 := eq530448 X0
       grind)
    | exact resolve eq530448 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq530448
  have eq530732 : ∀ X0 : G, (σ x) = (σ (k (M.op x y) (M.op (M.op x y) X0))) ∨ (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq1419 eq530641
    | (have j0 := eq530641 X0
       grind)
    | exact resolve eq530641 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530641
  have eq530799 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) ∨ (σ x) = (σ (k (M.op x y) (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq530732 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq530732
    | (have j0 := eq530732 X0
       grind)
    | exact resolve eq530732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530732
  have eq1133079 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) (M.op (M.op x y) X0))) ∨ (σ x) = (σ (k (M.op x y) (M.op (M.op x y) (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | exact superpose eq530799 eq369
    | (have j1 := eq530799 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq369 eq530799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq530799
  have eq1133169 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (σ x) = (σ (k (M.op x y) (M.op (M.op x y) (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | exact superpose eq1361 eq1133079
    | (have j0 := eq1133079 X0
       grind)
    | exact resolve eq1133079 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133079
  have eq1133242 : (σ x) = (σ (k (M.op x y) x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1361 eq1133169
    | exact resolve eq1133169 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361 eq1133169
  have eq1133243 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq119 eq1133242
    | exact resolve eq1133242 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133242
  have eq1133252 : (τ (σ x)) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1133243 eq130
    | exact resolve eq130 eq1133243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133243
  have eq1133331 : (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq28 eq1133252
    | exact resolve eq1133252 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133252
  have eq1133386 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op x y)) ∨ x = (k (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 X1 x
       have i₂ := eq1133331
       grind)
    | exact superpose eq1133331 eq360
    | exact resolve eq360 eq1133331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq1133331
  have eq1133487 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = (k (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq1133386 X0 x
       have i₂ := eq1342 X0 x
       grind)
    | exact superpose eq1342 eq1133386
    | exact resolve eq1133386 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342 eq1133386
  have eq1138389 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) y) ∨ (σ x) = (σ (k (M.op x y) (M.op (M.op x y) y))) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq1133487 eq453519
    | exact resolve eq453519 eq1133487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453519 eq1133487
  have eq1138865 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ (k (M.op x y) (M.op (M.op x y) y))) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq1138389
       have i₂ := eq4622 sF0
       grind)
    | exact superpose eq4622 eq1138389
    | exact resolve eq1138389 eq4622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4622 eq1138389
  have eq1138977 : x = (M.op x y) ∨ (σ x) = (σ (k (M.op x y) (M.op (M.op x y) y))) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq1419 eq1138865
    | exact resolve eq1138865 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138865
  have eq1139046 : (σ x) = (σ (k (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq1419 eq1138977
    | exact resolve eq1138977 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419 eq1138977
  have eq1139075 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq119 eq1139046
    | exact resolve eq1139046 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139046
  have eq1152572 : (τ (σ x)) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq1139075 eq130
    | exact resolve eq130 eq1139075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq1139075
  have eq1152655 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq28 eq1152572
    | exact resolve eq1152572 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1152572
  have eq1152656 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq1152655
  have eq1152668 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1152656 eq119
    | exact resolve eq119 eq1152656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq1152656
  have eq1152797 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1152668
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1152668
    | exact resolve eq1152668 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152668
  have eq1152840 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1152797
       have i₂ := eq87 sF1 sF2
       grind)
    | exact superpose eq87 eq1152797
    | (have j1 := eq87 x (σ x)
       grind)
    | exact resolve eq1152797 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq1152797
  have eq1161007 : (M.op (σ x) (σ x)) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1152840 eq1339
    | exact resolve eq1339 eq1152840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161013 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1582 eq1161007
    | exact resolve eq1161007 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161007
  have eq1161231 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1161013 eq1152840
    | exact resolve eq1152840 eq1161013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152840 eq1161013
  have eq1161329 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1161231
  have eq1161420 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1161329 eq390
    | exact resolve eq390 eq1161329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq1167973 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1161329 eq1161420
    | exact resolve eq1161420 eq1161329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161329 eq1161420
  have eq1168010 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1167973
  have eq1168060 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1168010 eq1339
    | exact resolve eq1339 eq1168010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168066 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1582 eq1168060
    | exact resolve eq1168060 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168060
  have eq1168096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1168066 eq1168010
    | exact resolve eq1168010 eq1168066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168010 eq1168066
  have eq1168118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1168096
  have eq1168120 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1168118
       have r₂ := eq27
       grind)
    | exact resolve eq1168118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168118
  have eq1168135 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1168120 eq1603
    | exact resolve eq1603 eq1168120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603 eq1168120
  have eq1168543 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1168135 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq1168135
       grind)
    | exact resolve eq13 eq1168135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168135
  have eq1168605 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1168543 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168543
  have eq1173672 : x = (τ (M.op (σ x) y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1168605 eq320197
    | exact resolve eq320197 eq1168605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320197
  have eq1173677 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1168605 eq322171
    | exact resolve eq322171 eq1168605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322171
  have eq1173926 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) y)) ∨ x = (M.op x y) := by grind
  clear eq1173677
  have eq1173931 : x = (τ (M.op (σ x) y)) ∨ x = (M.op x y) := by grind
  clear eq1173672
  have eq1174007 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1582 eq1173926
    | exact resolve eq1173926 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173926
  have eq1174010 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1582 eq1173931
    | exact resolve eq1173931 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173931
  have eq1182539 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1174007 eq1168605
    | exact resolve eq1168605 eq1174007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168605 eq1174007
  have eq1182560 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq1182539
  have eq1182568 : (k (σ x) (σ x)) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1341 eq1182560
    | exact resolve eq1182560 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341 eq1182560
  have eq1182580 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1582 eq1182568
    | exact resolve eq1182568 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182568
  have eq1182605 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1182580 eq49
    | exact resolve eq49 eq1182580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1182580
  have eq1183073 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3570 x
       have i₂ := eq1182605
       grind)
    | exact superpose eq1182605 eq3570
    | (have j0 := eq3570 x
       grind)
    | exact resolve eq3570 eq1182605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3570 eq1182605
  have eq1183423 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1183073
       have r₂ := eq1174010
       grind)
    | exact resolve eq1183073 eq1174010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174010 eq1183073
  have eq1183736 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1339 x x
       have i₂ := eq1183423
       grind)
    | exact superpose eq1183423 eq1339
    | exact resolve eq1339 eq1183423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183747 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1183736
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1183736
    | exact resolve eq1183736 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1183736
  have eq1183890 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1183423
       have i₂ := eq1183747
       grind)
    | exact superpose eq1183747 eq1183423
    | exact resolve eq1183423 eq1183747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183423 eq1183747
  have eq1184003 : x = (M.op x y) := by grind
  clear eq1183890
  have eq1184080 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1184003 eq20
    | exact resolve eq20 eq1184003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1184127 : x = (M.op x x) := by
    first
    | exact superpose eq1184003 eq1359
    | exact resolve eq1359 eq1184003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359 eq1184003
  have eq1184914 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1184080
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1184080
    | exact resolve eq1184080 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184080
  have eq1185026 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq1184914 eq1582
    | exact resolve eq1582 eq1184914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582
  have eq1186461 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1184127
       grind)
    | exact superpose eq1184127 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1184127
       grind)
    | exact resolve eq13 eq1184127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186522 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1186461 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186461
  have eq1194293 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq527 x
       have i₂ := eq1186522 x
       grind)
    | exact superpose eq1186522 eq527
    | (have j0 := eq527 x
       grind)
    | exact resolve eq527 eq1186522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq1186522
  have eq1195863 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1194293
       have i₂ := eq1184127
       grind)
    | exact superpose eq1184127 eq1194293
    | exact resolve eq1194293 eq1184127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184127 eq1194293
  have eq1195864 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1195863
  have eq1196413 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1195864
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1195864
    | exact resolve eq1195864 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1195864
  have eq1196802 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1184914 eq1196413
    | exact resolve eq1196413 eq1184914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184914 eq1196413
  have eq1198410 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq1196802 eq1339
    | exact resolve eq1339 eq1196802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq1198416 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1185026 eq1198410
    | exact resolve eq1198410 eq1185026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185026 eq1198410
  have eq1198467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1196802 eq1198416
    | exact resolve eq1198416 eq1196802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196802 eq1198416
  have eq1198499 : False := by grind
  exact eq1198499

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_x_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k y x) := by
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
  have eq75 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
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
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq92 y x
       grind)
    | exact superpose eq92 eq71
    | (have j1 := eq92 y x
       grind)
    | exact resolve eq71 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq92 sF3 sF2
       grind)
    | exact superpose eq92 eq81
    | (have j1 := eq92 (σ y) (σ x)
       grind)
    | exact resolve eq81 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq114 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq111
    | exact resolve eq111 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq116 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq114
    | exact resolve eq114 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
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
  clear eq117
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ y) (σ x)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq148 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq137 eq16
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq407 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq71
    | exact resolve eq71 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq116
  have eq410 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq407
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq514 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq127
  have eq515 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq514
  have eq520 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq515 eq118
    | exact resolve eq118 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq524 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq520
  have eq531 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq524
       have r₂ := eq129
       grind)
    | exact resolve eq524 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq524
  have eq535 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq531 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq531
       grind)
    | exact resolve eq13 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq536 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq535
  have eq537 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq536
    | exact resolve eq536 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq536
  have eq609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq537 eq118
    | exact resolve eq118 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq537
  have eq612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq609
  have eq616 : y = (M.op x y) := by
    first
    | (have r₁ := eq612
       have r₂ := eq27
       grind)
    | exact resolve eq612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq618 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq616 eq20
    | exact resolve eq20 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq622 : y ≠ y ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq616 eq74
    | (have r₁ := eq74
       have r₂ := eq616
       grind)
    | exact resolve eq74 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq628 : y = (M.op y x) ∨ y = (k y x) := by grind
  clear eq622
  have eq636 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq618
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq618
    | exact resolve eq618 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq649 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq636 eq410
    | exact resolve eq410 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq654 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq649
       have r₂ := eq27
       grind)
    | exact resolve eq649 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq666 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq654 eq148
    | exact resolve eq148 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq654
  have eq668 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq616 eq666
    | exact resolve eq666 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq948 : y = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq628
       have i₂ := eq668
       grind)
    | exact superpose eq668 eq628
    | exact resolve eq628 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq950 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq948
       grind)
    | exact superpose eq948 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq948
       grind)
    | exact resolve eq13 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq951 : (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq950
  have eq952 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq951
       have i₂ := eq668
       grind)
    | exact superpose eq668 eq951
    | exact resolve eq951 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq951
  have eq954 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq952
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq952
    | exact resolve eq952 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq952
  have eq956 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq616 eq954
    | exact resolve eq954 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq954
  have eq957 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq956
  have eq962 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq957 eq15
    | exact resolve eq15 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq979 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq962
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq962
    | exact resolve eq962 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq962
  have eq985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq636 eq979
    | exact resolve eq979 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq979
  have eq989 : False := by grind
  exact eq989

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_pyx_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (k (M.op (M.op X0 X1) (M.op X0 X1)) X2) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have i₂ := eq9 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq60
    | (have j0 := eq60 (σ X1) (σ X0)
       grind)
    | exact resolve eq60 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq36 (τ X0)
       grind)
    | exact superpose eq36 eq18
    | exact resolve eq18 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq87 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq87
    | exact resolve eq87 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq110 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq23 X2 X0 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq71 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq71 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq71 X0 X1
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq181 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq174 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq174 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq174 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq174 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq185 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq181
    | (have j0 := eq181 X0 X1
       grind)
    | exact resolve eq181 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq194 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (σ X0) (σ X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq23
    | exact resolve eq23 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) (σ X0) X1
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq23
    | exact resolve eq23 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (M.op X1 (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X2 (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 (M.op X2 (M.op X0 X1))
       have i₂ := eq23 X2 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq23 eq34
    | (have j0 := eq34 X0 X1 (M.op X2 (M.op X0 X1))
       grind)
    | (have r₁ := eq34 X0 X1 (M.op X0 (M.op X0 X1))
       have r₂ := eq23 X0 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq34 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1 X0
       have i₂ := eq24 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq34
    | (have j0 := eq34 X0 X1 X0
       grind)
    | (have r₁ := eq34 X0 x X0
       have r₂ := eq24 X0 x (M.op X0 x)
       grind)
    | exact resolve eq34 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq253 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq251 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq254 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X2 (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq250 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq737 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq169
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq169
    | (have j1 := eq60 (σ y) (σ x)
       grind)
    | exact resolve eq169 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq169
  have eq738 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq737
  have eq1456 : ∀ X0 X1 : G, (k (τ (M.op (M.op (σ X0) X1) (M.op (σ X0) X1))) X0) = (τ (M.op (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) X0
       have i₂ := eq253 (σ X0) X1
       grind)
    | exact superpose eq253 eq22
    | exact resolve eq22 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq253
  have eq2125 : ∀ X0 X1 : G, (k (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (M.op X1 (σ (M.op X0 X0)))) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq254 (σ X0) (σ X0) x
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq254
    | exact resolve eq254 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq2155 : ∀ X0 X1 : G, (k (σ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X1 (σ (M.op X0 X0)))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2125 X0 X1
       have i₂ := eq99 (M.op X0 X0)
       grind)
    | exact superpose eq99 eq2125
    | exact resolve eq2125 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2166 : ∀ X0 X1 : G, (k (σ X0) (M.op X1 (σ (M.op X0 X0)))) = (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2155 x X1
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq2155 X0 X1
       have i₂ := eq23 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq23 eq2155
    | exact resolve eq2155 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq2297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq185
    | (have j0 := eq185 X0 X1
       grind)
    | exact resolve eq185 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq2298 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2297 X0 X1
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq2297
    | (have j0 := eq2297 X0 X1
       grind)
    | exact resolve eq2297 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq4614 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq23 y x X0
       have i₂ := eq738
       grind)
    | exact superpose eq738 eq23
    | exact resolve eq23 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4615 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x y) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq24 y x x
       have i₂ := eq738
       grind)
    | exact superpose eq738 eq24
    | exact resolve eq24 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq7436 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ (M.op X0 X0))))) = (τ (M.op (σ X0) (M.op X1 (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op X1 (σ (M.op X0 X0)))
       have i₂ := eq2166 X0 X1
       grind)
    | exact superpose eq2166 eq31
    | exact resolve eq31 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2166
  have eq22759 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq7436 X0 (M.op (σ X0) X1)
       have i₂ := eq24 (σ X0) X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq24 eq7436
    | exact resolve eq7436 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7436
  have eq23257 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k y (τ (M.op (M.op (σ x) (σ y)) (σ (M.op y y))))) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq22759 y (σ x)
       have i₂ := eq4614 X0
       grind)
    | exact superpose eq4614 eq22759
    | (have j1 := eq4614 X0
       grind)
    | exact resolve eq22759 eq4614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4614
  have eq23493 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k y (τ (σ y))) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq23257 X0
       have i₂ := eq194 y (σ x)
       grind)
    | exact superpose eq194 eq23257
    | (have j0 := eq23257 X0
       grind)
    | exact resolve eq23257 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23257
  have eq23588 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k y y) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq23493 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq23493
    | (have j0 := eq23493 X0
       grind)
    | exact resolve eq23493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23493
  have eq23664 : ∀ X0 : G, (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq23588 X0
       have i₂ := eq36 y
       grind)
    | exact superpose eq36 eq23588
    | (have j0 := eq23588 X0
       grind)
    | exact resolve eq23588 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23588
  have eq24464 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq23664 X0
       grind)
    | exact superpose eq23664 eq11
    | (have j1 := eq23664 X0
       grind)
    | exact resolve eq11 eq23664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23664
  have eq25548 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq24464 X0
       grind)
    | exact superpose eq24464 eq16
    | (have j1 := eq24464 X0
       grind)
    | exact resolve eq16 eq24464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25558 : ∀ X0 : G, (k (τ (M.op (σ (M.op y y)) (σ (M.op y y)))) x) = (τ (M.op (M.op (σ (M.op y y)) (σ (M.op y y))) (σ x))) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1456 x (σ y)
       have i₂ := eq24464 X0
       grind)
    | exact superpose eq24464 eq1456
    | (have j1 := eq24464 X0
       grind)
    | exact resolve eq1456 eq24464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24464
  have eq25630 : ∀ X0 : G, (k (τ (σ (M.op (M.op y y) (M.op y y)))) x) = (τ (M.op (σ (M.op (M.op y y) (M.op y y))) (σ x))) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq25558 X0
       have i₂ := eq99 (M.op y y)
       grind)
    | exact superpose eq99 eq25558
    | (have j0 := eq25558 X0
       grind)
    | exact resolve eq25558 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25558
  have eq25650 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) = (k (τ (σ y)) x) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq25630 X0
       have i₂ := eq23 y y y
       grind)
    | (have i₁ := eq25630 X0
       have i₂ := eq23 X0 (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq23 eq25630
    | (have j0 := eq25630 X0
       grind)
    | exact resolve eq25630 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25630
  have eq25662 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq25650 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq25650
    | (have j0 := eq25650 X0
       grind)
    | exact resolve eq25650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25650
  have eq28151 : (M.op x y) = (M.op x x) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq24 x y (M.op x x)
       have i₂ := eq25662 x
       grind)
    | exact superpose eq25662 eq24
    | exact resolve eq24 eq25662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25662
  have eq28651 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq23 x y X0
       have i₂ := eq28151
       grind)
    | exact superpose eq28151 eq23
    | exact resolve eq23 eq28151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28151
  have eq65730 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4615 (M.op y x)
       have i₂ := eq23 x y x
       grind)
    | exact superpose eq23 eq4615
    | exact resolve eq4615 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4615
  have eq66411 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq195 y (σ x)
       have i₂ := eq65730
       grind)
    | exact superpose eq65730 eq195
    | exact resolve eq195 eq65730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq66745 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq110 (σ y) (σ (M.op y y)) (σ x)
       have i₂ := eq66411
       grind)
    | exact superpose eq66411 eq110
    | exact resolve eq110 eq66411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq66411
  have eq66796 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq66745
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq66745
    | exact resolve eq66745 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66745
  have eq66847 : (k (τ (M.op (σ (M.op y y)) (σ (M.op y y)))) x) = (τ (M.op (M.op (σ (M.op y y)) (σ (M.op y y))) (σ x))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1456 x (σ y)
       have i₂ := eq66796
       grind)
    | exact superpose eq66796 eq1456
    | exact resolve eq1456 eq66796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456
  have eq66856 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq199 y (σ x)
       have i₂ := eq66796
       grind)
    | exact superpose eq66796 eq199
    | (have j0 := eq199 y (σ x)
       grind)
    | (have r₁ := eq199 y (σ x)
       have r₂ := eq66796
       grind)
    | exact resolve eq199 eq66796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq66909 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq66856
  have eq66927 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq66909
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq66909
    | exact resolve eq66909 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66909
  have eq66931 : (k (τ (σ (M.op (M.op y y) (M.op y y)))) x) = (τ (M.op (σ (M.op (M.op y y) (M.op y y))) (σ x))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq66847
       have i₂ := eq99 (M.op y y)
       grind)
    | exact superpose eq99 eq66847
    | exact resolve eq66847 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66847
  have eq66957 : (τ (M.op (σ y) (σ x))) = (k (τ (σ y)) x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq66931
       have i₂ := eq23 y y y
       grind)
    | (have i₁ := eq66931
       have i₂ := eq23 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq23 eq66931
    | exact resolve eq66931 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66931
  have eq66969 : (M.op x y) = (M.op y y) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq66957
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq66957
    | exact resolve eq66957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66957
  have eq67623 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq65730
       have i₂ := eq66927
       grind)
    | exact superpose eq66927 eq65730
    | exact resolve eq65730 eq66927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65730 eq66927
  have eq67702 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq67623
  have eq67758 : y = (M.op (M.op x x) (M.op x y)) ∨ (k y x) = (τ (M.op (σ y) (σ x))) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq28651 y
       have i₂ := eq66969
       grind)
    | exact superpose eq66969 eq28651
    | exact resolve eq28651 eq66969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28651 eq66969
  have eq67865 : y = (M.op (M.op x x) (M.op x y)) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by grind
  clear eq67758
  have eq67872 : x = y ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq67865
       have i₂ := eq23 x x y
       grind)
    | (have i₁ := eq67865
       have i₂ := eq23 x (M.op (M.op x x) (M.op x y)) x
       grind)
    | exact superpose eq23 eq67865
    | exact resolve eq67865 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67865
  have eq68311 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67872
       grind)
    | exact superpose eq67872 eq16
    | exact resolve eq16 eq67872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67872
  have eq68343 : (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have r₁ := eq68311
       have r₂ := eq99 x
       grind)
    | exact resolve eq68311 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68311
  have eq68811 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ y) (σ x))
       have i₂ := eq68343
       grind)
    | exact superpose eq68343 eq11
    | exact resolve eq11 eq68343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68343
  have eq68996 : (σ x) = (M.op (σ (k y x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq194 x (σ y)
       have i₂ := eq68811
       grind)
    | exact superpose eq68811 eq194
    | exact resolve eq194 eq68811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq68811
  have eq76567 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2298 y x
       have i₂ := eq67702
       grind)
    | exact superpose eq67702 eq2298
    | (have j0 := eq2298 y x
       grind)
    | (have r₁ := eq2298 y x
       have r₂ := eq67702
       grind)
    | exact resolve eq2298 eq67702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298 eq67702
  have eq76647 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq76567
  have eq76648 : (M.op x y) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq76647
  have eq77333 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x X0)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq25548 X0
       have i₂ := eq76648
       grind)
    | exact superpose eq76648 eq25548
    | (have j0 := eq25548 X0
       grind)
    | exact resolve eq25548 eq76648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77401 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 y y
       have i₂ := eq76648
       grind)
    | exact superpose eq76648 eq23
    | exact resolve eq23 eq76648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76648
  have eq77448 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq77333 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77333
  have eq81465 : x = y ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77401 x
       have i₂ := eq77448 y
       grind)
    | exact superpose eq77448 eq77401
    | exact resolve eq77401 eq77448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77401 eq77448
  have eq81620 : x = y ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq81465
  have eq82340 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81620
       grind)
    | exact superpose eq81620 eq16
    | exact resolve eq16 eq81620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81620
  have eq82397 : (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq82340
       have r₂ := eq99 x
       grind)
    | exact resolve eq82340 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82340
  have eq83135 : (σ x) = (M.op (σ (M.op y y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq68996
       have i₂ := eq82397
       grind)
    | exact superpose eq82397 eq68996
    | exact resolve eq68996 eq82397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68996 eq82397
  have eq86565 : (τ (σ x)) = (k (M.op y y) (τ (M.op (σ x) (σ (M.op (M.op y y) (M.op y y)))))) := by
    first
    | (have i₁ := eq22759 (M.op y y) (σ (M.op x x))
       have i₂ := eq83135
       grind)
    | exact superpose eq83135 eq22759
    | exact resolve eq22759 eq83135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22759 eq83135
  have eq86671 : (τ (σ x)) = (k (M.op y y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq86565
       have i₂ := eq23 y y y
       grind)
    | (have i₁ := eq86565
       have i₂ := eq23 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq23 eq86565
    | exact resolve eq86565 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86565
  have eq86705 : x = (k (M.op y y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq86671
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq86671
    | exact resolve eq86671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86671
  have eq89400 : x = (k (M.op y y) (τ (σ (M.op y y)))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq86705
       have i₂ := eq66796
       grind)
    | exact superpose eq66796 eq86705
    | exact resolve eq86705 eq66796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66796 eq86705
  have eq89556 : x = (k (M.op y y) (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq89400
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq89400
    | exact resolve eq89400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89400
  have eq89619 : x = (M.op (M.op y y) (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq89556
       have i₂ := eq36 (M.op y y)
       grind)
    | exact superpose eq36 eq89556
    | exact resolve eq89556 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq89556
  have eq89665 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq89619
       have i₂ := eq23 y y y
       grind)
    | (have i₁ := eq89619
       have i₂ := eq23 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq23 eq89619
    | exact resolve eq89619 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89619
  have eq90285 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89665
       grind)
    | exact superpose eq89665 eq16
    | exact resolve eq16 eq89665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89665
  have eq90350 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq90285
       have r₂ := eq99 x
       grind)
    | exact resolve eq90285 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90285
  have eq90966 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq25548 X0
       have i₂ := eq90350
       grind)
    | exact superpose eq90350 eq25548
    | (have j0 := eq25548 X0
       grind)
    | exact resolve eq25548 eq90350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25548
  have eq91040 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 y y
       have i₂ := eq90350
       grind)
    | exact superpose eq90350 eq23
    | exact resolve eq23 eq90350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq90350
  have eq91091 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq90966 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90966
  have eq94998 : x = y := by
    first
    | (have i₁ := eq91091 y
       have i₂ := eq91040 x
       grind)
    | exact superpose eq91040 eq91091
    | exact resolve eq91091 eq91040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91040 eq91091
  have eq95826 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94998
       grind)
    | exact superpose eq94998 eq16
    | exact resolve eq16 eq94998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94998
  have eq95894 : False := by grind
  exact eq95894

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_pyx_pxx_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq99 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq99
    | exact resolve eq99 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq103 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq100
  have eq149 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq154 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq158 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq149
    | (have j0 := eq149 X0 X1
       grind)
    | exact resolve eq149 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq827 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq16
    | (have j1 := eq158 x y
       grind)
    | exact resolve eq16 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq908 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154
    | exact resolve eq154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq953 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq908 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq908
    | (have j0 := eq908 X0 X1
       grind)
    | exact resolve eq908 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq4450 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq827
       have i₂ := eq953 x y
       grind)
    | exact superpose eq953 eq827
    | (have j1 := eq953 x y
       grind)
    | (have r₁ := eq827
       have r₂ := eq953 x y
       grind)
    | (have r₁ := eq827
       have r₂ := eq953 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq827
       have r₂ := eq953 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq827 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq953
  have eq4451 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq4450
  have eq4453 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4451
       grind)
    | exact superpose eq4451 eq16
    | exact resolve eq16 eq4451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4451
  have eq4454 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4453
       have r₂ := eq82 x
       grind)
    | exact resolve eq4453 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453
  have eq4460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq4454
       grind)
    | exact superpose eq4454 eq103
    | exact resolve eq103 eq4454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4472 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4460
       have r₂ := eq16
       grind)
    | exact resolve eq4460 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4460
  have eq4475 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4472
       grind)
    | exact superpose eq4472 eq10
    | exact resolve eq10 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4472
  have eq4522 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4475
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4475
    | exact resolve eq4475 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4475
  have eq4525 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4522
       grind)
    | exact superpose eq4522 eq16
    | exact resolve eq16 eq4522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4522
  have eq4526 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4525
       have r₂ := eq82 x
       grind)
    | exact resolve eq4525 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq4525
  have eq4535 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4526
       grind)
    | exact superpose eq4526 eq10
    | exact resolve eq10 eq4526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4526
  have eq4582 : x = (M.op y y) := by
    first
    | (have i₁ := eq4535
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4535
    | exact resolve eq4535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4535
  have eq4596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq4582
       grind)
    | exact superpose eq4582 eq103
    | exact resolve eq103 eq4582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq4582
  have eq4607 : False := by grind
  exact eq4607

/-- `Equation2304`: `x = (y ◇ (x ◇ (y ◇ y))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxy_pyx_Equation2304 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2304 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2304.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2860 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq2929 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2860 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq2860
    | (have j0 := eq2860 X0 X1
       grind)
    | exact resolve eq2860 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq5594 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2929 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2929
    | exact resolve eq2929 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq5660 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5594 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq5594
    | (have j0 := eq5594 X0 X1
       grind)
    | exact resolve eq5594 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq5594
  have eq5691 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5660 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq5660 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq5660 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5660
  have eq5724 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5691 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5691
    | exact resolve eq5691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5755 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq5691 (σ X1) X0
       grind)
    | exact superpose eq5691 eq15
    | (have j1 := eq5691 (σ X0) X1
       grind)
    | exact resolve eq15 eq5691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5691
  have eq5818 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq5724 (τ X0) X1
       grind)
    | exact superpose eq5724 eq18
    | (have j1 := eq5724 X1 (τ X0)
       grind)
    | exact resolve eq18 eq5724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5724
  have eq6191 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5818 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5818
    | exact resolve eq5818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5818
  have eq6271 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6191 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6191
    | (have j0 := eq6191 X0 X1
       grind)
    | exact resolve eq6191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191
  have eq8903 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5755 x y
       grind)
    | exact superpose eq5755 eq16
    | (have j1 := eq5755 y x
       grind)
    | exact resolve eq16 eq5755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5755
  have eq8955 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8903
       have i₂ := eq6271 x y
       grind)
    | exact superpose eq6271 eq8903
    | (have j1 := eq6271 (σ y) (σ x)
       grind)
    | (have r₁ := eq8903
       have r₂ := eq6271 x y
       grind)
    | exact resolve eq8903 eq6271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8956 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq8955
  have eq8960 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq8956
       grind)
    | exact superpose eq8956 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8956
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8956
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8956
       grind)
    | exact resolve eq13 eq8956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8956
  have eq8964 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq8960
  have eq8965 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq8964
       have r₂ := eq12 y x
       grind)
    | exact resolve eq8964 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8964
  have eq8969 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq90 y (σ x)
       have i₂ := eq8965
       grind)
    | exact superpose eq8965 eq90
    | exact resolve eq90 eq8965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq8971 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq8965
       grind)
    | exact superpose eq8965 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8965
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8965
       grind)
    | exact resolve eq13 eq8965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8972 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq8965
       grind)
    | exact superpose eq8965 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8965
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8965
       grind)
    | exact resolve eq13 eq8965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8965
  have eq8974 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq8972
  have eq8975 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq8971
  have eq8977 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq8974
       have i₂ := eq76 y
       grind)
    | exact superpose eq76 eq8974
    | exact resolve eq8974 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq8974
  have eq8978 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq8975
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq8975 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8975
  have eq8980 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq8969
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8969
    | exact resolve eq8969 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8969
  have eq8983 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq8977
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8977
    | exact resolve eq8977 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8977
  have eq8984 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq8978
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8978
    | exact resolve eq8978 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8978
  have eq8985 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq8983
       have r₂ := eq8980
       grind)
    | exact resolve eq8983 eq8980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8980 eq8983
  have eq9003 : (σ (k y x)) = (σ (k x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq8984
       have i₂ := eq8985
       grind)
    | exact superpose eq8985 eq8984
    | exact resolve eq8984 eq8985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8984
  have eq9004 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8985
       grind)
    | exact superpose eq8985 eq16
    | exact resolve eq16 eq8985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8985
  have eq9014 : (M.op x y) = (k y x) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq9003
  have eq9028 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq8903
       have i₂ := eq9014
       grind)
    | exact superpose eq9014 eq8903
    | exact resolve eq8903 eq9014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9014
  have eq9029 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq9028
  have eq9035 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq9029
       grind)
    | exact superpose eq9029 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9029
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9029
       grind)
    | exact resolve eq13 eq9029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9029
  have eq9039 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq9035
  have eq9042 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq9039
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq9039 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9039
  have eq9048 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq9042
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9042
    | exact resolve eq9042 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9042
  have eq9078 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9048
       grind)
    | exact superpose eq9048 eq16
    | exact resolve eq16 eq9048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9048
  have eq9095 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq9078
       have i₂ := eq6271 x y
       grind)
    | exact superpose eq6271 eq9078
    | (have j1 := eq6271 y x
       grind)
    | (have r₁ := eq9078
       have r₂ := eq6271 x y
       grind)
    | exact resolve eq9078 eq6271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6271 eq9078
  have eq9096 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ (k x y)) := by grind
  clear eq9095
  have eq9101 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq9096
       grind)
    | exact superpose eq9096 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9096
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq9096
       grind)
    | exact resolve eq13 eq9096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9096
  have eq9105 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ (k x y)) := by grind
  clear eq9101
  have eq9106 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq9105
       have r₂ := eq12 y x
       grind)
    | exact resolve eq9105 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9105
  have eq9107 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq9106
       have r₂ := eq9004
       grind)
    | exact resolve eq9106 eq9004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9004 eq9106
  have eq9109 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8903
       have i₂ := eq9107
       grind)
    | exact superpose eq9107 eq8903
    | exact resolve eq8903 eq9107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8903
  have eq9110 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq9109
  have eq9241 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq9110
       grind)
    | exact superpose eq9110 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9110
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9110
       grind)
    | exact resolve eq13 eq9110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9110
  have eq9245 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq9241
  have eq9248 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq9245
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq9245 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9245
  have eq9254 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq9248
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9248
    | exact resolve eq9248 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9248
  have eq9257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9254
       have i₂ := eq9107
       grind)
    | exact superpose eq9107 eq9254
    | exact resolve eq9254 eq9107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9107 eq9254
  have eq9260 : False := by grind
  exact eq9260

/-- `Equation2310`: `x = (y ◇ (x ◇ (z ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_pxy_pyx_Equation2310 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2310 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2310.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op x (M.op X0 (M.op x X0)))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op x (M.op (M.op X0 (M.op X1 X0)) (M.op x (M.op X0 (M.op X1 X0))))) X1
       have i₂ := eq9 (M.op X0 (M.op X1 X0)) x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 (M.op x (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq61 (M.op X0 X0) x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq297 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq305 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X1 (M.op X2 X1)) X0) ∨ (M.op X0 X1) = X1 ∨ (M.op (M.op X1 (M.op X2 X1)) X0) = (k X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1))
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 (M.op X2 X1))
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq70 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq70
    | (have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq70 x
       have r₂ := eq14 x x
       grind)
    | (have r₁ := eq70 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq70 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq312 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq317 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq320 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq309 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq322 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq301 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq323 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq324 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq323 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq325 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq312
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq312
    | exact resolve eq312 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq326 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq320 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq320 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq320 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq337 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq61
    | (have j1 := eq318 X0
       grind)
    | exact resolve eq61 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq326 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq326
    | exact resolve eq326 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq326 (τ X0)
       grind)
    | exact superpose eq326 eq17
    | (have j1 := eq326 (τ X0)
       grind)
    | exact resolve eq17 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq363 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq357
    | (have j0 := eq357 X0
       grind)
    | exact resolve eq357 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq379 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq363 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq363
    | (have j0 := eq363 X0
       grind)
    | exact resolve eq363 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq410 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq322 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq322
    | (have j0 := eq322 (σ X0) (σ X1)
       grind)
    | exact resolve eq322 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq322 (τ X1) X0
       grind)
    | exact superpose eq322 eq17
    | (have j1 := eq322 (τ X1) X0
       grind)
    | exact resolve eq17 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq11
    | (have j1 := eq379 X0
       grind)
    | exact resolve eq11 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq537 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq536 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq536
    | (have j0 := eq536 X0
       grind)
    | exact resolve eq536 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq589 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq324 (σ X1) (σ X0)
       grind)
    | exact superpose eq324 eq15
    | (have j1 := eq324 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq589
    | (have j0 := eq589 X0 X1
       grind)
    | exact resolve eq589 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq669 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq537 x
       have i₂ := eq322 x x
       grind)
    | exact superpose eq322 eq537
    | (have j0 := eq537 X0
       have j1 := eq322 X0 X0
       grind)
    | exact resolve eq537 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq537
  have eq692 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq669 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq713 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq692 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq692 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq692 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq790 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq713 X0
       have i₂ := eq318 (τ X0)
       grind)
    | exact superpose eq318 eq713
    | (have j0 := eq713 X0
       have j1 := eq318 (τ X0)
       grind)
    | exact resolve eq713 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq809 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq790 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq790
    | (have j0 := eq790 X0
       grind)
    | exact resolve eq790 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq813 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq809 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq809 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq809 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq815 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq813 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq813
    | (have j0 := eq813 X0
       grind)
    | exact resolve eq813 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq854 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq815 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq815
    | (have j0 := eq815 (σ X0)
       grind)
    | exact resolve eq815 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq893 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq854 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq854
    | (have j0 := eq854 X0
       grind)
    | exact resolve eq854 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq854
  have eq896 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq893 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq893
    | (have j0 := eq893 X0
       grind)
    | exact resolve eq893 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq897 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq896 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq896
    | (have j0 := eq896 X0
       grind)
    | exact resolve eq896 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq6918 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq325
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq325
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq325 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6919 : (k x y) = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
  clear eq6918
  have eq14617 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X0 X1
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq305
    | (have j0 := eq305 X0 X0 x
       grind)
    | exact resolve eq305 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq39050 : ∀ X0 X1 : G, (k X1 (M.op X1 X0)) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14617 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14617
    | (have j0 := eq14617 X1 X1
       have j1 := eq14 X1 X1
       grind)
    | exact resolve eq14617 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14617
  have eq39256 : ∀ X0 X1 : G, (k X1 (M.op X1 X0)) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39050 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39050
  have eq46590 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq432
    | exact resolve eq432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq46872 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46590 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46590
    | (have j0 := eq46590 X0 X1
       grind)
    | exact resolve eq46590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46590
  have eq81904 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq410 X1 X0
       grind)
    | exact superpose eq410 eq10
    | (have j1 := eq410 X1 X0
       grind)
    | exact resolve eq10 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq81989 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81904 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81904
    | (have j0 := eq81904 X0 X1
       grind)
    | exact resolve eq81904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81904
  have eq109137 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq610 X1 X0
       grind)
    | exact superpose eq610 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq610 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq610 X0 X1
       grind)
    | exact resolve eq12 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109183 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq610 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq109213 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq109137 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq109137 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq109137 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109137
  have eq109326 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq109213 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq109213
    | (have j0 := eq109213 X0 X1
       grind)
    | exact resolve eq109213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109213
  have eq1212218 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81989 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81989
    | (have j0 := eq81989 X1 (τ X0)
       grind)
    | exact resolve eq81989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213259 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq81989 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81989
  have eq1213894 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1212218 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq1212218
    | (have j0 := eq1212218 X0 X1
       grind)
    | exact resolve eq1212218 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1212218
  have eq1225289 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq1213894 X1 X0
       grind)
    | exact superpose eq1213894 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq1213894 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) X0
       have r₂ := eq1213894 X0 X1
       grind)
    | exact resolve eq12 eq1213894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213894
  have eq1225536 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = X1 ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1225289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225289
  have eq1229094 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (k (τ (σ X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1225536 X0 (σ X1)
       grind)
    | exact superpose eq1225536 eq15
    | (have j1 := eq1225536 X0 (σ X1)
       grind)
    | exact resolve eq15 eq1225536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225536
  have eq1229273 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (τ (σ X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1229094 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1229094
    | (have j0 := eq1229094 X0 X1
       grind)
    | exact resolve eq1229094 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229094
  have eq1229428 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1229273 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1229273
    | (have j0 := eq1229273 X0 X1
       grind)
    | exact resolve eq1229273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229273
  have eq1357183 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq109326 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq109326
    | (have j0 := eq109326 (τ X0) (τ X1)
       grind)
    | exact resolve eq109326 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357648 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1357183 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1357183
    | (have j0 := eq1357183 X0 X1
       grind)
    | exact resolve eq1357183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357183
  have eq1357830 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1357648 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1357648
    | (have j0 := eq1357648 X0 X1
       grind)
    | exact resolve eq1357648 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357648
  have eq1357993 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1357830 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq1357830
    | (have j0 := eq1357830 X0 X1
       grind)
    | exact resolve eq1357830 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357830
  have eq1358133 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X0 X1) ≠ X1 ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1357993 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1357993
    | (have j0 := eq1357993 X0 X1
       grind)
    | exact resolve eq1357993 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357993
  have eq1358254 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1358133 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1358133
    | (have j0 := eq1358133 X0 X1
       grind)
    | exact resolve eq1358133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358133
  have eq1358330 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ X0))) = (k (σ (τ X1)) X0) ∨ (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1358254 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq1358254
    | (have j0 := eq1358254 X0 X1
       grind)
    | exact resolve eq1358254 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358254
  have eq1358367 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 (σ (τ X0))) ∨ (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1358330 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1358330
    | (have j0 := eq1358330 X0 X1
       grind)
    | exact resolve eq1358330 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358330
  have eq1358393 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1358367 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1358367
    | (have j0 := eq1358367 X0 X1
       grind)
    | exact resolve eq1358367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358367
  have eq1513483 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq1229428 X1 X0
       grind)
    | exact superpose eq1229428 eq10
    | (have j1 := eq1229428 X1 X0
       grind)
    | exact resolve eq10 eq1229428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229428
  have eq1513840 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1513483 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1513483
    | (have j0 := eq1513483 X0 X1
       grind)
    | exact resolve eq1513483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513483
  have eq1516033 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1513840 y x
       grind)
    | exact superpose eq1513840 eq16
    | (have j1 := eq1513840 y x
       grind)
    | exact resolve eq16 eq1513840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513840
  have eq1519287 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (k x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1516033
       have i₂ := eq324 y x
       grind)
    | exact superpose eq324 eq1516033
    | (have j1 := eq324 y x
       grind)
    | exact resolve eq1516033 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq1519292 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ y = (k x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1516033
       have i₂ := eq46872 y x
       grind)
    | exact superpose eq46872 eq1516033
    | (have j1 := eq46872 y x
       grind)
    | (have r₁ := eq1516033
       have r₂ := eq46872 y x
       grind)
    | exact resolve eq1516033 eq46872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46872 eq1516033
  have eq1519293 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1519292
  have eq1519294 : x = (k y x) ∨ y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1519293
  have eq1519299 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (k x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq1519287
  have eq1519300 : x = (M.op x y) ∨ y = (k x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq1519299
  have eq1519303 : x = (k y x) ∨ y = (k x y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1519294
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1519294 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519294
  have eq1519306 : y = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1519300
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1519300 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519300
  have eq1519313 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq109326 y x
       have i₂ := eq1519303
       grind)
    | exact superpose eq1519303 eq109326
    | (have j0 := eq109326 y x
       grind)
    | exact resolve eq109326 eq1519303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519303
  have eq1519318 : y = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq1519313
  have eq1519331 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq6919
       have i₂ := eq1519306
       grind)
    | exact superpose eq1519306 eq6919
    | exact resolve eq6919 eq1519306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1519335 : y ≠ y ∨ x = (k y x) ∨ (M.op y x) = (k y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1358393 x y
       have i₂ := eq1519306
       grind)
    | exact superpose eq1519306 eq1358393
    | (have j0 := eq1358393 x y
       grind)
    | (have r₁ := eq1358393 x y
       have r₂ := eq1519306
       grind)
    | exact resolve eq1358393 eq1519306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358393
  have eq1519337 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq1519306
  have eq1519338 : x = (k y x) ∨ (M.op y x) = (k y x) ∨ (M.op x y) = (k x y) := by grind
  clear eq1519335
  have eq1519341 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq1519331
  have eq1519383 : x ≠ (M.op y x) ∨ (M.op y x) = (k y x) ∨ (M.op x y) = (k x y) := by grind
  clear eq1519338
  have eq1522353 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1213259 y x
       have i₂ := eq1519341
       grind)
    | exact superpose eq1519341 eq1213259
    | (have j0 := eq1213259 y x
       grind)
    | exact resolve eq1213259 eq1519341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1522367 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq1522353
  have eq1550828 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1519318
       have i₂ := eq1519341
       grind)
    | exact superpose eq1519341 eq1519318
    | exact resolve eq1519318 eq1519341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519341
  have eq1550868 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1550828
       have r₂ := eq1522367
       grind)
    | exact resolve eq1550828 eq1522367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522367 eq1550828
  have eq1550872 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1550868
       have r₂ := eq16
       grind)
    | exact resolve eq1550868 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550868
  have eq1550880 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1550872
       grind)
    | exact superpose eq1550872 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1550872
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1550872
       grind)
    | exact resolve eq13 eq1550872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550872
  have eq1551030 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1550880
  have eq1551034 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1551030
       have r₂ := eq1519337
       grind)
    | exact resolve eq1551030 eq1519337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551030
  have eq1551632 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq109183 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq109183
    | (have j0 := eq109183 (τ X1) (τ X0)
       grind)
    | exact resolve eq109183 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1551835 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq109183 X0 X0
       have i₂ := eq897 X0
       grind)
    | exact superpose eq897 eq109183
    | (have j0 := eq109183 X0 X0
       have j1 := eq897 X0
       grind)
    | (have r₁ := eq109183 X0 X0
       have r₂ := eq897 X0
       grind)
    | exact resolve eq109183 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq109183
  have eq1552430 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1551835 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551835
  have eq1552431 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1552430 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552430
  have eq1553167 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1551632 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1551632
    | (have j0 := eq1551632 X0 X1
       grind)
    | exact resolve eq1551632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551632
  have eq1553376 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1553167 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1553167
    | (have j0 := eq1553167 X0 X1
       grind)
    | exact resolve eq1553167 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553167
  have eq1553544 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ X0))) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1553376 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq1553376
    | (have j0 := eq1553376 X0 X1
       grind)
    | exact resolve eq1553376 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1553376
  have eq1553703 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 (σ (τ X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1553544 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1553544
    | (have j0 := eq1553544 X0 X1
       grind)
    | exact resolve eq1553544 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553544
  have eq1553822 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1553703 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1553703
    | (have j0 := eq1553703 X0 X1
       grind)
    | exact resolve eq1553703 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553703
  have eq1553886 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1553822 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1553822
    | (have j0 := eq1553822 X0 X1
       grind)
    | exact resolve eq1553822 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553822
  have eq1553926 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1553886 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1553886
    | (have j0 := eq1553886 X0 X1
       grind)
    | exact resolve eq1553886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553886
  have eq1554550 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) X1
       have i₂ := eq1552431 X0
       grind)
    | exact superpose eq1552431 eq61
    | (have j1 := eq1552431 X0
       grind)
    | exact resolve eq61 eq1552431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552431
  have eq1750195 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1519318
       have i₂ := eq1551034
       grind)
    | exact superpose eq1551034 eq1519318
    | exact resolve eq1519318 eq1551034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519318
  have eq1750205 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1213259 y x
       have i₂ := eq1551034
       grind)
    | exact superpose eq1551034 eq1213259
    | (have j0 := eq1213259 y x
       grind)
    | exact resolve eq1213259 eq1551034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213259 eq1551034
  have eq1750219 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1750205
  have eq1750227 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1750195
       have r₂ := eq1750219
       grind)
    | exact resolve eq1750195 eq1750219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750195 eq1750219
  have eq1750229 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1750227
       have r₂ := eq16
       grind)
    | exact resolve eq1750227 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750227
  have eq1750233 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1519337
       have i₂ := eq1750229
       grind)
    | exact superpose eq1750229 eq1519337
    | (have r₁ := eq1519337
       have r₂ := eq1750229
       grind)
    | exact resolve eq1519337 eq1750229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1750398 : x ≠ y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  have eq1750408 : y = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1750233
  have eq1750425 : y = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1750408
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq1750408
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq1750408 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750408
  have eq1750441 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6919
       have i₂ := eq1750425
       grind)
    | exact superpose eq1750425 eq6919
    | exact resolve eq6919 eq1750425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6919
  have eq1750467 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1750441
  have eq1750484 : x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq62 x y
       have i₂ := eq1750467
       grind)
    | exact superpose eq1750467 eq62
    | exact resolve eq62 eq1750467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1750672 : x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1750484
       have i₂ := eq1750229
       grind)
    | exact superpose eq1750229 eq1750484
    | exact resolve eq1750484 eq1750229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750229 eq1750484
  have eq1750852 : x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1750672
  have eq1752579 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1750467
       have i₂ := eq1750852
       grind)
    | exact superpose eq1750852 eq1750467
    | exact resolve eq1750467 eq1750852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750467 eq1750852
  have eq1752750 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1752579
  have eq1752775 : x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1752750
       have r₂ := eq1750398
       grind)
    | exact resolve eq1752750 eq1750398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750398 eq1752750
  have eq1752789 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq325
       have i₂ := eq1752775
       grind)
    | exact superpose eq1752775 eq325
    | exact resolve eq325 eq1752775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq1752775
  have eq1752962 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1752789
  have eq1752963 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
  clear eq1752962
  have eq1795807 : (σ y) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
  clear eq1752963
  have eq1796474 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1795807
       have i₂ := eq1750425
       grind)
    | exact superpose eq1750425 eq1795807
    | exact resolve eq1795807 eq1750425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750425
  have eq1796488 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1796474
  have eq1796489 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1796488
  have eq1796518 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq1554550 x (σ y)
       have i₂ := eq1796489
       grind)
    | exact superpose eq1796489 eq1554550
    | (have j0 := eq1554550 x x
       grind)
    | exact resolve eq1554550 eq1796489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554550
  have eq1796521 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq1796489
       grind)
    | exact superpose eq1796489 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1796489
       grind)
    | exact resolve eq12 eq1796489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1796535 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq337 (σ x) (σ y)
       have i₂ := eq1796489
       grind)
    | exact superpose eq1796489 eq337
    | (have j0 := eq337 (σ x) x
       grind)
    | exact resolve eq337 eq1796489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq1796680 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1796521
  have eq1796799 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1796535
       have i₂ := eq1796489
       grind)
    | exact superpose eq1796489 eq1796535
    | exact resolve eq1796535 eq1796489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796535
  have eq1796802 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1796680
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1796680
    | exact resolve eq1796680 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796680
  have eq1796804 : (σ x) = (σ y) ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq1796518
       have i₂ := eq1796489
       grind)
    | exact superpose eq1796489 eq1796518
    | exact resolve eq1796518 eq1796489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796489 eq1796518
  have eq1796894 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq1796799
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1796799
    | exact resolve eq1796799 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796799
  have eq1796962 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq109326 y x
       have i₂ := eq1796802
       grind)
    | exact superpose eq1796802 eq109326
    | (have j0 := eq109326 y x
       grind)
    | (have r₁ := eq109326 y x
       have r₂ := eq1796802
       grind)
    | exact resolve eq109326 eq1796802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109326
  have eq1796965 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1796802
       grind)
    | exact superpose eq1796802 eq10
    | exact resolve eq10 eq1796802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796802
  have eq1797341 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq1796962
  have eq1797359 : x = (k y x) := by
    first
    | (have i₁ := eq1796965
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1796965
    | exact resolve eq1796965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796965
  have eq1797381 : x ≠ x ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1553926 y x
       have i₂ := eq1797359
       grind)
    | exact superpose eq1797359 eq1553926
    | (have j0 := eq1553926 y x
       grind)
    | (have r₁ := eq1553926 y x
       have r₂ := eq1797359
       grind)
    | exact resolve eq1553926 eq1797359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553926
  have eq1797382 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1797381
  have eq1808893 : y = (τ (σ x)) ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1796804
       grind)
    | exact superpose eq1796804 eq10
    | exact resolve eq10 eq1796804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796804
  have eq1809285 : x = y ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq1808893
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1808893
    | exact resolve eq1808893 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808893
  have eq1809305 : x ≠ (M.op x x) ∨ (M.op x x) = (k x x) ∨ (M.op x x) = (k x x) ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq1519383
       have i₂ := eq1809285
       grind)
    | exact superpose eq1809285 eq1519383
    | exact resolve eq1519383 eq1809285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519383 eq1809285
  have eq1809426 : x ≠ (M.op x x) ∨ (M.op x x) = (k x x) := by grind
  clear eq1809305
  have eq1809451 : (M.op x x) = (k x x) := by
    first
    | (have j1 := eq318 x
       grind)
    | (have r₁ := eq1809426
       have r₂ := eq318 x
       grind)
    | exact resolve eq1809426 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq1809426
  have eq1823023 : y = (τ (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1796894
       grind)
    | exact superpose eq1796894 eq10
    | exact resolve eq10 eq1796894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796894
  have eq1823655 : x = y ∨ (M.op (σ x) (σ x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq1823023
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1823023
    | exact resolve eq1823023 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823023
  have eq1823674 : x = y ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1823655
       have i₂ := eq1809451
       grind)
    | exact superpose eq1809451 eq1823655
    | exact resolve eq1823655 eq1809451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823655
  have eq1823784 : (σ x) ≠ (σ (k x x)) ∨ (M.op (σ x) (σ x)) = (σ (k x x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1795807
       have i₂ := eq1823674
       grind)
    | exact superpose eq1823674 eq1795807
    | exact resolve eq1795807 eq1823674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795807 eq1823674
  have eq1823818 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq340 x
       grind)
    | (have r₁ := eq1823784
       have r₂ := eq340 x
       grind)
    | exact resolve eq1823784 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq1823784
  have eq1823833 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1823818
       have i₂ := eq1809451
       grind)
    | exact superpose eq1809451 eq1823818
    | exact resolve eq1823818 eq1809451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809451 eq1823818
  have eq1823834 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq1823833
  have eq1843849 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1797341
       grind)
    | exact superpose eq1797341 eq16
    | exact resolve eq16 eq1797341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797341
  have eq1845984 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1843849
       have i₂ := eq1797382
       grind)
    | exact superpose eq1797382 eq1843849
    | exact resolve eq1843849 eq1797382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797382 eq1843849
  have eq1845991 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1845984
  have eq1846013 : x ≠ y ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1519337
       have i₂ := eq1845991
       grind)
    | exact superpose eq1845991 eq1519337
    | exact resolve eq1519337 eq1845991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846021 : x ≠ x ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1845991
       grind)
    | exact superpose eq1845991 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1845991
       grind)
    | exact resolve eq12 eq1845991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846022 : x ≠ x ∨ y = (M.op y x) ∨ (M.op y x) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1845991
       grind)
    | exact superpose eq1845991 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1845991
       grind)
    | exact resolve eq13 eq1845991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846023 : y = (M.op (M.op y x) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq1845991
       grind)
    | exact superpose eq1845991 eq62
    | exact resolve eq62 eq1845991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1846179 : y = (M.op y x) ∨ (M.op y x) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1846022
  have eq1846180 : y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1846021
  have eq1846184 : y = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1846179
       have i₂ := eq1797359
       grind)
    | exact superpose eq1797359 eq1846179
    | exact resolve eq1846179 eq1797359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846179
  have eq1874627 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1846023
       have i₂ := eq1846184
       grind)
    | exact superpose eq1846184 eq1846023
    | exact resolve eq1846023 eq1846184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846023 eq1846184
  have eq1874906 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq1874627
  have eq1875982 : y = (k y x) ∨ y = (M.op y y) ∨ x = y ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq39256 x y
       have i₂ := eq1874906
       grind)
    | exact superpose eq1874906 eq39256
    | (have j0 := eq39256 y y
       grind)
    | exact resolve eq39256 eq1874906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874906
  have eq1876066 : y = (k y x) ∨ y = (M.op y y) ∨ x = y ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1875982
  have eq1876080 : y = (k y x) ∨ y = (M.op y y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1876066
       have r₂ := eq1846013
       grind)
    | exact resolve eq1876066 eq1846013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876066
  have eq1876089 : x = y ∨ y = (M.op y y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1876080
       have i₂ := eq1797359
       grind)
    | exact superpose eq1797359 eq1876080
    | exact resolve eq1876080 eq1797359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876080
  have eq1876090 : x = (k x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1876089
       have r₂ := eq1846013
       grind)
    | exact resolve eq1876089 eq1846013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846013 eq1876089
  have eq1878411 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1846180
       have i₂ := eq1876090
       grind)
    | exact superpose eq1876090 eq1846180
    | exact resolve eq1846180 eq1876090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846180 eq1876090
  have eq1878437 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq1878411
  have eq1878474 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1878437
       grind)
    | exact superpose eq1878437 eq16
    | exact resolve eq16 eq1878437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878437
  have eq1878760 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1878474
       have r₂ := eq1823834
       grind)
    | exact resolve eq1878474 eq1823834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878474
  have eq1878788 : (M.op x y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq1878760
       grind)
    | exact superpose eq1878760 eq10
    | exact resolve eq10 eq1878760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878760
  have eq1879178 : y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1878788
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1878788
    | exact resolve eq1878788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878788
  have eq1879191 : y ≠ y ∨ y = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1519337
       have i₂ := eq1879178
       grind)
    | exact superpose eq1879178 eq1519337
    | (have r₁ := eq1519337
       have r₂ := eq1879178
       grind)
    | exact resolve eq1519337 eq1879178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519337
  have eq1879209 : x = (M.op y x) ∨ x = y ∨ y = (k y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq299 y x
       have i₂ := eq1879178
       grind)
    | exact superpose eq1879178 eq299
    | (have j0 := eq299 y y
       grind)
    | exact resolve eq299 eq1879178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879178
  have eq1879493 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq1879191
  have eq1879518 : x = y ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1879209
       have i₂ := eq1797359
       grind)
    | exact superpose eq1797359 eq1879209
    | exact resolve eq1879209 eq1797359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879209
  have eq1879519 : x = (M.op y x) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq1879518
  have eq1879715 : y = (k y x) ∨ y = (M.op y y) ∨ x = y ∨ x = (k x y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq39256 x y
       have i₂ := eq1879519
       grind)
    | exact superpose eq1879519 eq39256
    | (have j0 := eq39256 y y
       grind)
    | exact resolve eq39256 eq1879519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39256 eq1879519
  have eq1879799 : y = (k y x) ∨ y = (M.op y y) ∨ x = y ∨ x = (k x y) := by grind
  clear eq1879715
  have eq1879829 : x = y ∨ y = (M.op y y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq1879799
       have i₂ := eq1797359
       grind)
    | exact superpose eq1797359 eq1879799
    | exact resolve eq1879799 eq1797359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879799
  have eq1879830 : x = (k x y) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq1879829
  have eq1885651 : x = y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1879493
       have i₂ := eq1879830
       grind)
    | exact superpose eq1879830 eq1879493
    | exact resolve eq1879493 eq1879830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879493 eq1879830
  have eq1885681 : x = y ∨ y = (M.op y y) := by grind
  clear eq1885651
  have eq1885729 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1885681
       grind)
    | exact superpose eq1885681 eq16
    | exact resolve eq16 eq1885681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885681
  have eq1886001 : y = (M.op y y) := by
    first
    | (have r₁ := eq1885729
       have r₂ := eq1823834
       grind)
    | exact resolve eq1885729 eq1823834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885729
  have eq1886028 : ∀ X0 : G, y = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq61 y X0
       have i₂ := eq1886001
       grind)
    | exact superpose eq1886001 eq61
    | exact resolve eq61 eq1886001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1886001
  have eq1887214 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1886028 x
       have i₂ := eq1845991
       grind)
    | exact superpose eq1845991 eq1886028
    | exact resolve eq1886028 eq1845991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886028
  have eq1896096 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1887214
       have i₂ := eq1845991
       grind)
    | exact superpose eq1845991 eq1887214
    | exact resolve eq1887214 eq1845991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845991 eq1887214
  have eq1902628 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1896096
       grind)
    | exact superpose eq1896096 eq16
    | exact resolve eq16 eq1896096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896096
  have eq1902921 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1902628
       have r₂ := eq1823834
       grind)
    | exact resolve eq1902628 eq1823834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902628
  have eq1902941 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq1902921
       grind)
    | exact superpose eq1902921 eq10
    | exact resolve eq10 eq1902921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902921
  have eq1903468 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1902941
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1902941
    | exact resolve eq1902941 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902941
  have eq1903609 : x = (M.op y x) ∨ x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq299 y x
       have i₂ := eq1903468
       grind)
    | exact superpose eq1903468 eq299
    | exact resolve eq299 eq1903468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq1903793 : x = y ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1903609
       have i₂ := eq1797359
       grind)
    | exact superpose eq1797359 eq1903609
    | exact resolve eq1903609 eq1797359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903609
  have eq1903794 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1903793
  have eq1903890 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq1903794
       grind)
    | exact superpose eq1903794 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq1903794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903794
  have eq1904063 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq1903890
  have eq1904081 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1904063
       have i₂ := eq1797359
       grind)
    | exact superpose eq1797359 eq1904063
    | exact resolve eq1904063 eq1797359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797359 eq1904063
  have eq1904082 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1904081
  have eq1904113 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1903468
       have i₂ := eq1904082
       grind)
    | exact superpose eq1904082 eq1903468
    | exact resolve eq1903468 eq1904082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903468 eq1904082
  have eq1904283 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1904113
  have eq1904308 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1904283
       grind)
    | exact superpose eq1904283 eq16
    | exact resolve eq16 eq1904283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904283
  have eq1904601 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1904308
       have r₂ := eq1823834
       grind)
    | exact resolve eq1904308 eq1823834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904308
  have eq1904613 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1904601
       grind)
    | exact superpose eq1904601 eq16
    | exact resolve eq16 eq1904601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1904638 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1904601
       grind)
    | exact superpose eq1904601 eq10
    | exact resolve eq10 eq1904601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904601
  have eq1905174 : x = y := by
    first
    | (have i₁ := eq1904638
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1904638
    | exact resolve eq1904638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904638
  have eq1905176 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1904613
       have i₂ := eq1823834
       grind)
    | exact superpose eq1823834 eq1904613
    | exact resolve eq1904613 eq1823834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823834 eq1904613
  have eq1905306 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1905176
       have i₂ := eq1905174
       grind)
    | exact superpose eq1905174 eq1905176
    | exact resolve eq1905176 eq1905174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905174 eq1905176
  have eq1905307 : False := by grind
  exact eq1905307

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq76 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq172 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq182 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq183 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq182 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq187 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | exact resolve eq183 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq188 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq561 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq188 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188
    | exact resolve eq188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq188 x y
       grind)
    | exact superpose eq188 eq16
    | (have j1 := eq188 x y
       grind)
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq592 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq561 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq561
    | (have j0 := eq561 X0 X1
       grind)
    | exact resolve eq561 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq561
  have eq593 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq592
    | exact resolve eq592 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq654 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq593 (τ X1) X0
       grind)
    | exact superpose eq593 eq18
    | (have j1 := eq593 (τ X1) X0
       grind)
    | exact resolve eq18 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq593
  have eq849 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq654
    | exact resolve eq654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq904 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq849 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq849
    | (have j0 := eq849 X0 X1
       grind)
    | exact resolve eq849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq969 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq575
       have i₂ := eq904 y x
       grind)
    | exact superpose eq904 eq575
    | (have j1 := eq904 (σ y) (σ x)
       grind)
    | (have r₁ := eq575
       have r₂ := eq904 y x
       grind)
    | exact resolve eq575 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq969
  have eq1003 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq970
  have eq1012 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq575
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq575
    | exact resolve eq575 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq1003
  have eq1013 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1012
  have eq1014 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1013
  have eq1027 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1014
  have eq1038 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1027
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1027
    | exact resolve eq1027 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1043 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1038
       grind)
    | exact superpose eq1038 eq16
    | exact resolve eq16 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1091 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1043
       have i₂ := eq904 y x
       grind)
    | exact superpose eq904 eq1043
    | (have j1 := eq904 y x
       grind)
    | (have r₁ := eq1043
       have r₂ := eq904 y x
       grind)
    | exact resolve eq1043 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq1092 : y = (M.op x x) := by grind
  clear eq1091
  have eq1099 : (M.op x y) = (k y x) := by grind
  clear eq1092
  have eq1147 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1043
       have i₂ := eq1099
       grind)
    | exact superpose eq1099 eq1043
    | exact resolve eq1043 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043 eq1099
  have eq1150 : False := by grind
  exact eq1150

/-- `Equation258`: `x = ((x ◇ x) ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyy_x_pxy_pyx_Equation258 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law258 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law258.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq34 (M.op X0 X0)
       grind)
    | exact superpose eq34 eq14
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq44 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq34 X0
       grind)
    | exact resolve eq13 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : y ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq48 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq44 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq37
  have eq62 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq54
       grind)
    | exact superpose eq54 eq16
    | exact resolve eq16 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq86 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = (M.op y x) := by
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
  have eq98 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq117 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39
    | (have j0 := eq39 x
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq128 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq117 eq16
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq146 : (σ (k (k y x) x)) = (k (k (σ y) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq41 (k y x)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq41
    | exact resolve eq41 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq239 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq16
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq320 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq16
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq368 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq71
    | (have j0 := eq71 (σ X0)
       grind)
    | exact resolve eq71 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq54
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq54
    | (have j1 := eq71 x
       grind)
    | exact resolve eq54 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq373 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq71 y
       grind)
    | exact superpose eq71 eq87
    | (have j1 := eq71 y
       grind)
    | exact resolve eq87 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq506 : ∀ X0 : G, (k (k y x) (τ X0)) = (τ (k (k (σ y) (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq320 (k y x) X0
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq320
    | exact resolve eq320 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq676 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq49 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq49 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq49 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq49 X0 X0
       grind)
    | exact resolve eq12 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq688 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq676 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq691 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq688
    | (have j0 := eq688 X0 X1
       grind)
    | exact resolve eq688 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq3193 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq14
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3194 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq34
    | exact resolve eq34 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3295 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq368 X0
       grind)
    | exact superpose eq368 eq34
    | (have j1 := eq368 X0
       grind)
    | exact resolve eq34 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5951 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X1 X0
       have i₂ := eq368 X0
       grind)
    | exact superpose eq368 eq685
    | (have j0 := eq685 X1 X0
       have j1 := eq368 X0
       grind)
    | (have r₁ := eq685 X0 X0
       have r₂ := eq368 X0
       grind)
    | exact resolve eq685 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq5953 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5951 X0 X1
       have j1 := eq685 X1 X0
       grind)
    | (have r₁ := eq5951 X1 X1
       have r₂ := eq685 X0 X1
       grind)
    | (have r₁ := eq5951 X1 X1
       have r₂ := eq685 X0 X1
       grind)
    | exact resolve eq5951 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5951
  have eq6791 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq691 X0 X1
       have j1 := eq685 X1 X0
       grind)
    | (have r₁ := eq691 X1 X1
       have r₂ := eq685 X0 X1
       grind)
    | (have r₁ := eq691 X1 X1
       have r₂ := eq685 X0 X1
       grind)
    | exact resolve eq691 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq691
  have eq7021 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq6791 X0 X1
       grind)
    | exact superpose eq6791 eq34
    | (have j1 := eq6791 X1 X0
       grind)
    | exact resolve eq34 eq6791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq7028 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (k (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq6791 X1 X0
       grind)
    | exact superpose eq6791 eq13
    | (have j0 := eq13 (σ X1) (σ X1)
       have j1 := eq6791 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq6791 X0 X1
       grind)
    | exact resolve eq13 eq6791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6791
  have eq7034 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7028 X0 X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq7028
    | (have j0 := eq7028 X0 X1
       grind)
    | exact resolve eq7028 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7028
  have eq13396 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3193 X0 X2
       have i₂ := eq3193 X0 X1
       grind)
    | exact superpose eq3193 eq3193
    | exact resolve eq3193 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13423 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3194 X0
       have i₂ := eq3193 X0 X1
       grind)
    | exact superpose eq3193 eq3194
    | exact resolve eq3194 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3194
  have eq13424 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0
       have i₂ := eq3193 X0 X1
       grind)
    | exact superpose eq3193 eq35
    | exact resolve eq35 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq13429 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X2
       have i₂ := eq3193 X0 X1
       grind)
    | exact superpose eq3193 eq14
    | exact resolve eq14 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193
  have eq13478 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq13423 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13423
    | (have j0 := eq13423 x y
       grind)
    | exact resolve eq13423 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13480 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq13423
    | (have j0 := eq13423 (σ x) (σ y)
       grind)
    | exact resolve eq13423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13521 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq13478 eq13396
    | exact resolve eq13396 eq13478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13478
  have eq13522 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq13480 eq13396
    | exact resolve eq13396 eq13480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13480
  have eq13540 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13396 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13396
    | (have j0 := eq13396 x y X0
       grind)
    | exact resolve eq13396 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13542 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq26 eq13396
    | (have j0 := eq13396 (σ x) (σ y) X0
       grind)
    | exact resolve eq13396 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13959 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq13521 y
       have i₂ := eq13396 sF0 y x
       grind)
    | (have i₁ := eq13521 y
       have i₂ := eq13396 sF0 x y
       grind)
    | exact superpose eq13396 eq13521
    | exact resolve eq13521 eq13396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13521
  have eq18408 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13424 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13424
    | exact resolve eq13424 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18601 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq13522 eq13429
    | exact resolve eq13429 eq13522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13522
  have eq18603 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13429 X0 X1 X1
       have i₂ := eq13396 (M.op X0 X1) X1 X2
       grind)
    | (have i₁ := eq13429 X0 X1 X1
       have i₂ := eq13396 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq13396 eq13429
    | exact resolve eq13429 eq13396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13396 eq13429
  have eq19049 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq18601 eq14
    | exact resolve eq14 eq18601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18601
  have eq19215 : y = (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13424 y x
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq13424
    | exact resolve eq13424 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq19222 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19215
       have i₂ := eq13424 x x
       grind)
    | exact superpose eq13424 eq19215
    | exact resolve eq19215 eq13424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19215
  have eq22880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq19222 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq19222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq22880
    | exact resolve eq22880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22880
  have eq22892 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq22881
       have r₂ := eq27
       grind)
    | exact resolve eq22881 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22881
  have eq23176 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ x) (σ x)) (σ x))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq22892 eq13424
    | exact resolve eq13424 eq22892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22892
  have eq23195 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq23176
       have i₂ := eq13424 sF2 sF2
       grind)
    | exact superpose eq13424 eq23176
    | exact resolve eq23176 eq13424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23176
  have eq23203 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq23195 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq23195
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq23195
       grind)
    | exact resolve eq13 eq23195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23195
  have eq23217 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq23203
  have eq23229 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq23217 eq96
    | exact resolve eq96 eq23217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq23236 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq23217 eq19222
    | exact resolve eq19222 eq23217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23217
  have eq23238 : x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq23236
  have eq23246 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq23229
    | exact resolve eq23229 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23229
  have eq23249 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq23246
       have r₂ := eq13 y x
       grind)
    | exact resolve eq23246 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23246
  have eq23527 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq23249
       grind)
    | exact superpose eq23249 eq86
    | exact resolve eq86 eq23249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23531 : (σ (k y x)) = (k (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq146
       have i₂ := eq23249
       grind)
    | exact superpose eq23249 eq146
    | exact resolve eq146 eq23249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq23535 : ∀ X0 : G, (k y (τ X0)) = (τ (k (k (σ y) (σ x)) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq506 X0
       have i₂ := eq23249
       grind)
    | exact superpose eq23249 eq506
    | exact resolve eq506 eq23249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq23249
  have eq23538 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (k (σ y) (σ x)) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq23535 X0
       have i₂ := eq239 X0
       grind)
    | exact superpose eq239 eq23535
    | exact resolve eq23535 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq23535
  have eq23542 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23531
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq23531
    | exact resolve eq23531 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq23531
  have eq23546 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23527
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23527
    | exact resolve eq23527 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23527
  have eq23587 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x X0) X0) x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18603 y x X0
       have i₂ := eq23238
       grind)
    | exact superpose eq23238 eq18603
    | exact resolve eq18603 eq23238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23238
  have eq23592 : x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23587 x
       have i₂ := eq13423 x x
       grind)
    | exact superpose eq13423 eq23587
    | exact resolve eq23587 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23587
  have eq23874 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq373
       have i₂ := eq23592
       grind)
    | exact superpose eq23592 eq373
    | exact resolve eq373 eq23592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq23902 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18408 y y
       have i₂ := eq23592
       grind)
    | exact superpose eq23592 eq18408
    | exact resolve eq18408 eq23592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23592
  have eq23908 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq23874
  have eq23912 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23902
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23902
    | exact resolve eq23902 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23902
  have eq23927 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23908
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23908
    | exact resolve eq23908 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23908
  have eq24919 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq372
       have i₂ := eq23912
       grind)
    | exact superpose eq23912 eq372
    | exact resolve eq372 eq23912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23912
  have eq24966 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq24919
    | exact resolve eq24919 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24919
  have eq25849 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq23927
       have i₂ := eq71 sF3
       grind)
    | exact superpose eq71 eq23927
    | (have j1 := eq71 (σ y)
       grind)
    | exact resolve eq23927 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27378 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq19222 eq23542
    | exact resolve eq23542 eq19222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23542
  have eq27384 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq27378
  have eq34074 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq27384 eq128
    | exact resolve eq128 eq27384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27384
  have eq34088 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq34074
    | exact resolve eq34074 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34074
  have eq42832 : ∀ X0 : G, (σ (τ (k (σ y) X0))) = (k (k (σ y) (σ x)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23538 eq15
    | exact resolve eq15 eq23538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23538
  have eq43083 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ y) (σ x)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq42832 X0
       have i₂ := eq15 (k sF3 X0)
       grind)
    | exact superpose eq15 eq42832
    | exact resolve eq42832 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42832
  have eq43113 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq19222 eq43083
    | exact resolve eq43083 eq19222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19222 eq43083
  have eq43200 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq43113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43113
  have eq82956 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq43200 eq23546
    | exact resolve eq23546 eq43200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23546 eq43200
  have eq83134 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq82956
  have eq83366 : (τ (σ y)) = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq83134 eq128
    | exact resolve eq128 eq83134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq83134
  have eq83383 : y = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq83366
    | exact resolve eq83366 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83366
  have eq84071 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq83383 eq34088
    | exact resolve eq34088 eq83383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34088 eq83383
  have eq84073 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq84071
  have eq84699 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13424 y x
       have i₂ := eq84073
       grind)
    | exact superpose eq84073 eq13424
    | exact resolve eq13424 eq84073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84073
  have eq84728 : y = (M.op (M.op x x) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84699
       have i₂ := eq18408 x x
       grind)
    | exact superpose eq18408 eq84699
    | exact resolve eq84699 eq18408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84699
  have eq84733 : y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84728
       have i₂ := eq13540 x
       grind)
    | exact superpose eq13540 eq84728
    | exact resolve eq84728 eq13540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13540 eq84728
  have eq241236 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7034 X0 X1
       have j1 := eq5953 X1 X0
       grind)
    | (have r₁ := eq7034 X0 X0
       have r₂ := eq5953 X0 X1
       grind)
    | exact resolve eq7034 eq5953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953 eq7034
  have eq429214 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq25849 eq48
    | exact resolve eq48 eq25849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25849
  have eq479937 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq429214 eq23927
    | exact resolve eq23927 eq429214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23927 eq429214
  have eq480019 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq479937
  have eq480137 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq480019 eq13423
    | exact resolve eq13423 eq480019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480143 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq480019 eq18408
    | exact resolve eq18408 eq480019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480019
  have eq480210 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq480143
    | exact resolve eq480143 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480143
  have eq480216 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13542 eq480137
    | exact resolve eq480137 eq13542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480137
  have eq482972 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq480210 eq12
    | exact resolve eq12 eq480210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480210
  have eq482988 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq482972
  have eq515316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq482988 eq24966
    | exact resolve eq24966 eq482988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24966 eq482988
  have eq515341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq515316
  have eq515347 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq515341
       have r₂ := eq27
       grind)
    | exact resolve eq515341 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515341
  have eq515652 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq515347 eq480216
    | exact resolve eq480216 eq515347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480216
  have eq515710 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq515652
  have eq516010 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq515710
    | exact resolve eq515710 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515710
  have eq517488 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq516010 eq515347
    | exact resolve eq515347 eq516010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515347 eq516010
  have eq517489 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq517488
  have eq518825 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq517489 eq29
    | exact resolve eq29 eq517489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517489
  have eq519076 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq518825
    | exact resolve eq518825 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518825
  have eq519077 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq519076
  have eq519079 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq519077 eq26
    | exact resolve eq26 eq519077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519080 : y = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq519077 eq29
    | exact resolve eq29 eq519077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520229 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq519080
    | exact resolve eq519080 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq519080
  have eq520231 : y ≠ y ∨ x = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq520229 eq46
    | (have r₁ := eq46
       have r₂ := eq520229
       grind)
    | exact resolve eq46 eq520229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq520419 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq520229 eq13959
    | exact resolve eq13959 eq520229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13959 eq520229
  have eq520950 : x = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq520231
  have eq520952 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq520419 x
       have i₂ := eq13423 y x
       grind)
    | exact superpose eq13423 eq520419
    | exact resolve eq520419 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520419
  have eq522344 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq519079 eq13542
    | exact resolve eq13542 eq519079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519079
  have eq522387 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7021 x y
       have i₂ := eq520950
       grind)
    | exact superpose eq520950 eq7021
    | (have j0 := eq7021 y x
       grind)
    | exact resolve eq7021 eq520950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7021 eq520950
  have eq522391 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq522387
  have eq522397 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq522391
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq522391
    | exact resolve eq522391 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522391
  have eq522423 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq522397
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq522397
    | exact resolve eq522397 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522397
  have eq522434 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq522423
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq522423
    | exact resolve eq522423 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522423
  have eq522443 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq522434
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq522434
    | exact resolve eq522434 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522434
  have eq522450 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq522443
    | exact resolve eq522443 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522443
  have eq522555 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq520952
       grind)
    | exact superpose eq520952 eq12
    | exact resolve eq12 eq520952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520952
  have eq522571 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = (M.op x y) := by grind
  clear eq522555
  have eq522572 : y = (k x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq522571
  have eq523969 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3295 x
       have i₂ := eq522572
       grind)
    | exact superpose eq522572 eq3295
    | (have j0 := eq3295 x
       grind)
    | exact resolve eq3295 eq522572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295 eq522572
  have eq524008 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq523969
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq523969
    | exact resolve eq523969 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523969
  have eq524038 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq524008
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq524008
    | exact resolve eq524008 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524008
  have eq524052 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq524038
    | exact resolve eq524038 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524038
  have eq524063 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq524052
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq524052
    | exact resolve eq524052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524052
  have eq619616 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq519077 eq522450
    | exact resolve eq522450 eq519077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522450
  have eq619754 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq619616
  have eq619773 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq619754
       have r₂ := eq27
       grind)
    | exact resolve eq619754 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619754
  have eq619782 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq619773 eq13424
    | exact resolve eq13424 eq619773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13424 eq619773
  have eq619795 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq619782
       have i₂ := eq18408 sF2 sF2
       grind)
    | exact superpose eq18408 eq619782
    | exact resolve eq619782 eq18408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18408 eq619782
  have eq619796 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq13542 eq619795
    | exact resolve eq619795 eq13542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13542 eq619795
  have eq619971 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq619796 eq522344
    | exact resolve eq522344 eq619796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522344
  have eq619986 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq619796 eq13423
    | exact resolve eq13423 eq619796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620004 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq619971
  have eq620199 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ (M.op x y)) X0) X0) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq620004 eq18603
    | exact resolve eq18603 eq620004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620004
  have eq620217 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq620199 x
       have i₂ := eq13423 sF1 x
       grind)
    | exact superpose eq13423 eq620199
    | exact resolve eq620199 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620199
  have eq620628 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq620217 eq19049
    | exact resolve eq19049 eq620217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19049 eq620217
  have eq624922 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq620628 eq619986
    | exact resolve eq619986 eq620628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619986 eq620628
  have eq624949 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq624922
  have eq625025 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq624949 eq18603
    | exact resolve eq18603 eq624949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18603 eq624949
  have eq625079 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq625025 x
       have i₂ := eq13423 sF4 x
       grind)
    | exact superpose eq13423 eq625025
    | exact resolve eq625025 eq13423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13423 eq625025
  have eq661495 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq524063 eq625079
    | exact resolve eq625079 eq524063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524063 eq625079
  have eq661538 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq661495
  have eq661614 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq661538 eq27
    | exact resolve eq27 eq661538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661538
  have eq661914 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq661614
       have r₂ := eq519077
       grind)
    | exact resolve eq661614 eq519077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519077 eq661614
  have eq662252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq661914 eq619796
    | exact resolve eq619796 eq661914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619796 eq661914
  have eq662343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq662252
  have eq662686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq662343
    | exact resolve eq662343 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662343
  have eq662823 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq662686
       have r₂ := eq27
       grind)
    | exact resolve eq662686 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662686
  have eq663253 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq662823 eq84733
    | exact resolve eq84733 eq662823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84733
  have eq663910 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq663253
  have eq664252 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq663910
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq663910
    | exact resolve eq663910 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663910
  have eq670353 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq664252 eq29
    | exact resolve eq29 eq664252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq664252
  have eq670692 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq670353
    | exact resolve eq670353 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670353
  have eq670693 : y = (M.op x y) ∨ x = y := by grind
  clear eq670692
  have eq671201 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq670693 eq662823
    | exact resolve eq662823 eq670693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662823 eq670693
  have eq671216 : x = y := by grind
  clear eq671201
  have eq671765 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq671216
       grind)
    | exact superpose eq671216 eq18
    | exact resolve eq18 eq671216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq671766 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq671216
       grind)
    | exact superpose eq671216 eq24
    | exact resolve eq24 eq671216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq671216
  have eq672112 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq671766
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq671766
    | exact resolve eq671766 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671766
  have eq672115 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq672112 eq26
    | exact resolve eq26 eq672112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq672112
  have eq672573 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq372
       have i₂ := eq671765
       grind)
    | exact superpose eq671765 eq372
    | exact resolve eq372 eq671765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq672658 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq671765
       grind)
    | exact superpose eq671765 eq13
    | (have j0 := eq13 x x
       grind)
    | exact resolve eq13 eq671765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671765
  have eq672689 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq672573
    | exact resolve eq672573 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672573
  have eq672753 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq672115 eq48
    | exact resolve eq48 eq672115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq730439 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq672689 eq71
    | (have j0 := eq71 (σ x)
       grind)
    | exact resolve eq71 eq672689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq730475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq672115 eq730439
    | exact resolve eq730439 eq672115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730439
  have eq730493 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq730475
       have r₂ := eq27
       grind)
    | exact resolve eq730475 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730475
  have eq730500 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq672115 eq730493
    | exact resolve eq730493 eq672115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730493
  have eq730511 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq730500 eq27
    | exact resolve eq27 eq730500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730897 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq730500 eq672753
    | exact resolve eq672753 eq730500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672753 eq730500
  have eq731383 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq730897 eq62
    | exact resolve eq62 eq730897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq731415 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq730897 eq672689
    | exact resolve eq672689 eq730897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672689 eq730897
  have eq731452 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq731415
  have eq731480 : x = (M.op x y) := by
    first
    | (have r₁ := eq731452
       have r₂ := eq730511
       grind)
    | exact resolve eq731452 eq730511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730511 eq731452
  have eq731495 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq731383
    | exact resolve eq731383 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq731383
  have eq731514 : x = (k x x) := by
    first
    | (have r₁ := eq731495
       have r₂ := eq672658
       grind)
    | exact resolve eq731495 eq672658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672658 eq731495
  have eq731542 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq731480 eq20
    | exact resolve eq20 eq731480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq731480
  have eq732720 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq731542
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq731542
    | exact resolve eq731542 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731542
  have eq734088 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq241236 x x
       have i₂ := eq731514
       grind)
    | exact superpose eq731514 eq241236
    | (have j0 := eq241236 x x
       grind)
    | exact resolve eq241236 eq731514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241236 eq731514
  have eq734089 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq734088
  have eq734090 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq734089
  have eq734113 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq734090
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq734090
    | exact resolve eq734090 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq734090
  have eq734146 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq672115 eq734113
    | exact resolve eq734113 eq672115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672115 eq734113
  have eq734176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq732720 eq734146
    | exact resolve eq734146 eq732720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732720 eq734146
  have eq734202 : False := by grind
  exact eq734202
