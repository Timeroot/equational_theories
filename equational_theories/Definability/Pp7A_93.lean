import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4542`: `x ◇ (y ◇ z) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyy_y_pxy_pxx_pxy_Equation4542 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4542 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4542.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X2) := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X3 X0)) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X3 X0)
       have i₂ := eq14 X1 X3 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 X0) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X2 X0))) = (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X2 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X3 X0)) = (M.op (M.op X0 X2) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq50 X0 x X2 X3
       have i₂ := eq14 X2 (M.op X0 x) X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq10
    | exact resolve eq10 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq73
    | exact resolve eq73 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq44
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq44 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq109 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq113 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq71 sF3
       grind)
    | exact superpose eq71 eq109
    | exact resolve eq109 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq115 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq71 y
       grind)
    | exact superpose eq71 eq113
    | exact resolve eq113 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq134 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq16
    | exact resolve eq16 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq152 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq149
       have i₂ := eq71 sF1
       grind)
    | exact superpose eq71 eq149
    | exact resolve eq149 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq154 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq152
       have i₂ := eq71 sF0
       grind)
    | exact superpose eq71 eq152
    | exact resolve eq152 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq234 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq82 (σ X0) sF1
       grind)
    | exact superpose eq82 eq41
    | (have j1 := eq82 X0 (σ (M.op x y))
       grind)
    | exact resolve eq41 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq262 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq82 x (τ X0)
       grind)
    | exact superpose eq82 eq42
    | (have j1 := eq82 X0 (τ X0)
       grind)
    | exact resolve eq42 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
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
  clear eq42
  have eq344 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq71 (τ X0)
       grind)
    | exact superpose eq71 eq34
    | exact resolve eq34 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq82 (τ X0) X1
       grind)
    | exact superpose eq82 eq34
    | (have j1 := eq82 X0 X1
       grind)
    | exact resolve eq34 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq353 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) y)) = (k (k X0 (σ X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq40
    | exact resolve eq40 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq40
  have eq355 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq344 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq344
    | exact resolve eq344 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq357 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq355 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq355
    | exact resolve eq355 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq355
  have eq388 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq475 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57
    | (have j0 := eq57 X0 X1 y x
       grind)
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op X4 X0)) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X3 X2) X4 X0
       have i₂ := eq57 X0 X3 X2 X1
       grind)
    | (have i₁ := eq14 (M.op X3 X2) X4 X0
       have i₂ := eq57 X0 X1 X2 X3
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x y)) = (M.op X2 (M.op X0 (M.op X1 y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq475 X2 (M.op y X0)
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq475
    | exact resolve eq475 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq475 X0 x
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq475
    | (have j1 := eq14 X0 x y
       grind)
    | exact resolve eq475 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X2 : G, (M.op X2 (M.op x y)) = (M.op X2 (M.op X0 (M.op x y))) := by
    intro X0 X2
    first
    | (have i₁ := eq519 X0 x X2
       have i₂ := eq475 X0 x
       grind)
    | (have i₁ := eq519 X0 x X2
       have i₂ := eq475 X0 x
       grind)
    | exact superpose eq475 eq519
    | (have j0 := eq519 X0 x X2
       grind)
    | exact resolve eq519 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq542 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op X2 (M.op X0 (M.op X1 (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq477 X0 (M.op sF3 X0)
       have i₂ := eq14 X0 X1 sF3
       grind)
    | exact superpose eq14 eq477
    | exact resolve eq477 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq477 X0 x
       have i₂ := eq14 X0 x sF3
       grind)
    | exact superpose eq14 eq477
    | (have j1 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq477 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op X2 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X2
    first
    | exact superpose eq477 eq542
    | (have j0 := eq542 X0 (σ x) X2
       grind)
    | exact resolve eq542 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq588 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 X4 (M.op X2 X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op X5 X3)) = (M.op X4 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq57 X4 X5 X3 (M.op X3 X0)
       have i₂ := eq51 X1 X2 X3 X0
       grind)
    | exact superpose eq51 eq57
    | exact resolve eq57 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq975 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq59 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59
    | (have j0 := eq59 y X0 x
       grind)
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ y) X0 (σ x)
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq545 eq977
    | exact resolve eq977 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1028 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq975 X0
       have i₂ := eq522 X0
       grind)
    | exact superpose eq522 eq975
    | exact resolve eq975 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1076 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq477 eq1026
    | exact resolve eq1026 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1026 eq1076
    | exact resolve eq1076 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1100 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1028 (M.op x y)
       have i₂ := eq475 sF0 x
       grind)
    | (have i₁ := eq1028 (M.op x y)
       have i₂ := eq475 sF0 x
       grind)
    | exact superpose eq475 eq1028
    | exact resolve eq1028 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1121 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1028 eq1100
    | exact resolve eq1100 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1649 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op y X1))) = (M.op (M.op X1 (M.op x y)) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 X1 x y X0
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1651 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (M.op (σ y) X1))) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 X1 (σ x) (σ y) X0
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1743 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X2 X0)) (M.op x y)) = (M.op X0 (M.op X1 (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq541 X2 (M.op sF0 (M.op X1 X2))
       have i₂ := eq54 sF0 X1 X2 x
       grind)
    | exact superpose eq54 eq541
    | exact resolve eq541 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq1745 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X2 X0)) (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq564 X2 (M.op sF4 (M.op X1 X2))
       have i₂ := eq54 sF4 X1 X2 x
       grind)
    | exact superpose eq54 eq564
    | exact resolve eq564 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq564
  have eq1762 : ∀ X0 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X2 X0)) (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | (have i₁ := eq1745 x X0 X2
       have i₂ := eq51 X0 x sF4 x
       grind)
    | exact superpose eq51 eq1745
    | exact resolve eq1745 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq1764 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op (M.op (M.op x y) (M.op X2 X0)) (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq1743 x X0 X2
       have i₂ := eq51 X0 x sF0 x
       grind)
    | exact superpose eq51 eq1743
    | exact resolve eq1743 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1840 : ∀ X0 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (M.op X2 X0) (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq1026 eq1762
    | exact resolve eq1762 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq1842 : ∀ X0 X2 : G, (M.op (M.op X2 X0) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0 X2
    first
    | exact superpose eq1028 eq1764
    | exact resolve eq1764 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq1888 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X2 X0) (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq1026 eq1840
    | exact resolve eq1840 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq1889 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op (M.op X2 X0) (M.op x y)) := by
    intro X0 X2
    first
    | exact superpose eq1028 eq1842
    | exact resolve eq1842 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq2003 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1026 eq1091
    | exact resolve eq1091 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2862 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1028 eq1121
    | exact resolve eq1121 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq2919 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) := by
    first
    | exact superpose eq2862 eq154
    | exact resolve eq154 eq2862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2948 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq78 (M.op y y)
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq78
    | exact resolve eq78 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2993 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op x y))) := by
    first
    | (have i₁ := eq2948
       have i₂ := eq475 (M.op y y) y
       grind)
    | exact superpose eq475 eq2948
    | exact resolve eq2948 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2948
  have eq2996 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1121 eq2993
    | exact resolve eq2993 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121 eq2993
  have eq2998 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq477 eq2996
    | exact resolve eq2996 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq2999 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1091 eq2998
    | exact resolve eq2998 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq2998
  have eq3000 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2003 eq2999
    | exact resolve eq2999 eq2003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999
  have eq3001 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq154 eq3000
    | exact resolve eq3000 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq3000
  have eq3014 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3001 eq59
    | exact resolve eq59 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3021 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq3014 x
       have i₂ := eq59 sF1 x sF1
       grind)
    | exact superpose eq59 eq3014
    | exact resolve eq3014 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq3014
  have eq3032 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1026 eq3021
    | exact resolve eq3021 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq3021
  have eq3075 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq348 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq348
    | (have j0 := eq348 X0 y
       grind)
    | exact resolve eq348 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3175 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq357 X0
       grind)
    | exact superpose eq357 eq16
    | exact resolve eq16 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq6586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq102 eq82
    | (have j0 := eq82 x (σ y)
       grind)
    | exact resolve eq82 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq6587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq6586
    | exact resolve eq6586 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6586
  have eq6590 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq6587
       have r₂ := eq27
       grind)
    | exact resolve eq6587 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6587
  have eq6592 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6590 eq134
    | exact resolve eq134 eq6590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq6590
  have eq6630 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq6592
    | exact resolve eq6592 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6592
  have eq6631 : y = (M.op y y) := by grind
  clear eq6630
  have eq6643 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq6631
       grind)
    | exact superpose eq6631 eq115
    | exact resolve eq115 eq6631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq6644 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq522 y
       have i₂ := eq6631
       grind)
    | exact superpose eq6631 eq522
    | exact resolve eq522 eq6631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6648 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq475 X0 y
       have i₂ := eq6631
       grind)
    | exact superpose eq6631 eq475
    | exact resolve eq475 eq6631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq6680 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq6644
       have i₂ := eq6631
       grind)
    | exact superpose eq6631 eq6644
    | exact resolve eq6644 eq6631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6644
  have eq6681 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6643
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6643
    | exact resolve eq6643 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6643
  have eq6749 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6680 eq2919
    | exact resolve eq2919 eq6680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq6786 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6749
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6749
    | exact resolve eq6749 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6749
  have eq6806 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq6681 eq477
    | exact resolve eq477 eq6681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7319 : ∀ X0 X1 : G, (σ (M.op (τ X0) (M.op (σ x) (σ y)))) = (k X0 (σ (M.op X1 (σ y)))) ∨ (M.op X1 (σ y)) = (M.op (M.op X1 (σ y)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq477 eq345
    | (have j0 := eq345 X0 (M.op X1 (σ y))
       grind)
    | exact resolve eq345 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7322 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6648 eq345
    | (have j0 := eq345 X0 (M.op x y)
       grind)
    | exact resolve eq345 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq7347 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq7322
    | (have j0 := eq7322 X0
       grind)
    | exact resolve eq7322 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7322
  have eq7350 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X1 (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op (τ X0) (M.op (σ x) (σ y)))) = (k X0 (σ (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq477 eq7319
    | (have j0 := eq7319 X0 X1
       grind)
    | exact resolve eq7319 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7319
  have eq7361 : ∀ X0 : G, (M.op x y) = (M.op y (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | exact superpose eq2862 eq7347
    | (have j0 := eq7347 X0
       grind)
    | exact resolve eq7347 eq2862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862 eq7347
  have eq7364 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op (τ X0) (M.op (σ x) (σ y)))) = (k X0 (σ (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq1888 eq7350
    | (have j0 := eq7350 X0 X1
       grind)
    | exact resolve eq7350 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7350
  have eq7371 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6680 eq7361
    | (have j0 := eq7361 X0
       grind)
    | exact resolve eq7361 eq6680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7361
  have eq7374 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X1 (σ y)) ∨ (σ (M.op (τ X0) (M.op (σ x) (σ y)))) = (k X0 (σ (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq3001 eq7364
    | (have j0 := eq7364 X0 X1
       grind)
    | exact resolve eq7364 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7364
  have eq7381 : ∀ X0 X1 : G, (σ y) = (M.op X1 (σ y)) ∨ (σ (M.op (τ X0) (M.op (σ x) (σ y)))) = (k X0 (σ (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq6786 eq7374
    | (have j0 := eq7374 X0 X1
       grind)
    | exact resolve eq7374 eq6786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7374
  have eq7579 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq6806 eq2003
    | exact resolve eq2003 eq6806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7582 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq3001 eq7579
    | exact resolve eq7579 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7579
  have eq7640 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq6786 eq7582
    | exact resolve eq7582 eq6786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7582
  have eq9381 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X2 X1)) y) = (M.op (M.op X0 X1) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 y X2 X1 X0 y
       have i₂ := eq6631
       grind)
    | exact superpose eq6631 eq503
    | exact resolve eq503 eq6631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9396 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op X2 X1)) (σ y)) = (M.op (M.op X0 X1) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq6681 eq503
    | exact resolve eq503 eq6681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq9893 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq545 eq9396
    | exact resolve eq9396 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9396
  have eq9903 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op x y)) = (M.op (M.op X0 X1) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9381 X0 X1 X2
       have i₂ := eq522 (M.op X2 X1)
       grind)
    | exact superpose eq522 eq9381
    | exact resolve eq9381 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9381
  have eq10075 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1888 eq9893
    | exact resolve eq9893 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9893
  have eq10083 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 X1) y) := by
    intro X0 X1
    first
    | exact superpose eq1889 eq9903
    | exact resolve eq9903 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889 eq9903
  have eq10169 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 X1) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq6806 eq10075
    | exact resolve eq10075 eq6806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10075
  have eq10176 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X1) y) := by
    intro X0 X1
    first
    | exact superpose eq6648 eq10083
    | exact resolve eq10083 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10083
  have eq11540 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 (σ (M.op x y)))))) = (M.op X1 (σ (k X0 (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1 X2 X3 X4
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f11540_13 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op X5 X3)) = (M.op X4 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
      intro X0 X1 X2 X3 X4 X5
      grind
    have f11540_14 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
      intro X0
      grind
    have f11540_20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X2) := by
      intro X0 X1 X2
      grind
    have f11540_23 : (M.op X1 (M.op X2 (M.op X3 (M.op X4 (σ (M.op x y)))))) ≠ (M.op X1 (σ (k X0 (M.op x y)))) := by grind
    have f11540_24 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
    have f11540_26 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) := by
      intro X0
      first
      | (have j0 := f11540_14 X0
         grind)
      | (have r₁ := f11540_14 X0
         have r₂ := f11540_24
         grind)
      | exact resolve f11540_14 f11540_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11540_38 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f11540_20 X0 X1 X2
         have i₂ := f11540_20 X0 X3 X2
         grind)
      | exact superpose f11540_20 f11540_20
      | exact resolve f11540_20 f11540_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11540_109 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) X1) (σ (M.op x y))) = (M.op X1 (σ (k X0 (M.op x y)))) := by
      intro X0 X1
      first
      | (have i₁ := f11540_20 X1 (σ X0) (σ (M.op x y))
         have i₂ := f11540_26 X0
         grind)
      | exact superpose f11540_26 f11540_20
      | exact resolve f11540_20 f11540_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11540_161 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X3 X4)))) = (M.op (M.op X4 X0) X4) := by
      intro X0 X1 X2 X3 X4
      first
      | (have i₁ := f11540_20 X0 x X4
         have i₂ := f11540_13 X1 X2 X3 X4 X0 x
         grind)
      | exact superpose f11540_13 f11540_20
      | exact resolve f11540_20 f11540_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11540_304 : ∀ X0 : G, (M.op X1 (σ (k X0 (M.op x y)))) ≠ (M.op X1 (M.op X2 (M.op X3 (M.op X0 (σ (M.op x y)))))) := by
      intro X0
      first
      | (have i₁ := f11540_23
         have i₂ := f11540_38 X3 X4 (σ (M.op x y)) X0
         grind)
      | (have i₁ := f11540_23
         have i₂ := f11540_38 X3 X0 (σ (M.op x y)) X4
         grind)
      | exact superpose f11540_38 f11540_23
      | exact resolve f11540_23 f11540_38
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11540_305 : (M.op X1 (σ (k X0 (M.op x y)))) ≠ (M.op (M.op (σ (M.op x y)) X1) (σ (M.op x y))) := by
      first
      | (have i₁ := f11540_304 x
         have i₂ := f11540_161 X1 X2 X3 x (σ (M.op x y))
         grind)
      | exact superpose f11540_161 f11540_304
      | exact resolve f11540_304 f11540_161
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f11540_311 : False := by
      first
      | (have r₁ := f11540_305
         have r₂ := f11540_109 X0 X1
         grind)
      | exact resolve f11540_305 f11540_109
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f11540_311
  clear eq234 eq609
  have eq12063 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) X1) (σ (M.op x y))) = (M.op X1 (σ (k X0 (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq11540 X0 x x X0 X1
       have i₂ := eq588 X0 X1 sF1 x x
       grind)
    | exact superpose eq588 eq11540
    | exact resolve eq11540 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq11540
  have eq12172 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X1 (σ (k X0 (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq3032 eq12063
    | exact resolve eq12063 eq3032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3032 eq12063
  have eq12227 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (k X0 (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq6806 eq12172
    | exact resolve eq12172 eq6806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12172
  have eq12260 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (k X0 (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq6786 eq12227
    | (have j0 := eq12227 X0 X1
       grind)
    | exact resolve eq12227 eq6786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12227
  have eq27622 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op y X1))) = (M.op (M.op X1 y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq6648 eq1649
    | exact resolve eq1649 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649 eq6648
  have eq27844 : ∀ X0 X1 : G, (M.op y y) ≠ (M.op y (M.op X0 (M.op y y))) ∨ (M.op X1 X1) = (M.op y (M.op X0 (M.op y y))) ∨ (M.op X1 X1) = (k X1 (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op y y)
       have i₂ := eq27622 X0 y
       grind)
    | exact superpose eq27622 eq12
    | (have j0 := eq12 X1 (M.op y y)
       grind)
    | exact resolve eq12 eq27622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27622
  have eq27930 : ∀ X0 X1 : G, (M.op y y) ≠ (M.op (M.op y y) y) ∨ (M.op X1 X1) = (M.op y (M.op X0 (M.op y y))) ∨ (M.op X1 X1) = (k X1 (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq27844 X0 X1
       have i₂ := eq51 X0 y y y
       grind)
    | exact superpose eq51 eq27844
    | (have j0 := eq27844 X0 X1
       grind)
    | exact resolve eq27844 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27844
  have eq28084 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op y (M.op X0 (M.op y y))) ∨ (M.op X1 X1) = (k X1 (M.op y y)) := by
    intro X0 X1
    first
    | (have j0 := eq27930 X0 X1
       grind)
    | (have r₁ := eq27930 X0 X1
       have r₂ := eq10176 y y
       grind)
    | exact resolve eq27930 eq10176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10176 eq27930
  have eq28161 : ∀ X1 : G, (M.op X1 X1) = (M.op (M.op y y) y) ∨ (M.op X1 X1) = (k X1 (M.op y y)) := by
    intro X1
    first
    | (have i₁ := eq28084 x X1
       have i₂ := eq51 x y y y
       grind)
    | exact superpose eq51 eq28084
    | (have j0 := eq28084 x X1
       grind)
    | exact resolve eq28084 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28084
  have eq28202 : ∀ X1 : G, (M.op X1 X1) = (M.op y (M.op x y)) ∨ (M.op X1 X1) = (k X1 (M.op y y)) := by
    intro X1
    first
    | (have i₁ := eq28161 X1
       have i₂ := eq522 y
       grind)
    | exact superpose eq522 eq28161
    | (have j0 := eq28161 X1
       grind)
    | exact resolve eq28161 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq28161
  have eq28217 : ∀ X1 : G, (M.op X1 X1) = y ∨ (M.op X1 X1) = (k X1 (M.op y y)) := by
    intro X1
    first
    | exact superpose eq6680 eq28202
    | (have j0 := eq28202 X1
       grind)
    | exact resolve eq28202 eq6680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6680 eq28202
  have eq28228 : ∀ X1 : G, (M.op X1 X1) = (k X1 y) ∨ (M.op X1 X1) = y := by
    intro X1
    first
    | (have i₁ := eq28217 X1
       have i₂ := eq6631
       grind)
    | exact superpose eq6631 eq28217
    | (have j0 := eq28217 X1
       grind)
    | exact resolve eq28217 eq6631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6631 eq28217
  have eq28236 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (M.op (σ y) X1))) = (M.op (M.op X1 (σ y)) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6806 eq1651
    | exact resolve eq1651 eq6806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq28607 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ y) (M.op X0 (M.op (σ y) (σ y)))) ∨ (M.op X1 X1) = (M.op (σ y) (M.op X0 (M.op (σ y) (σ y)))) ∨ (M.op X1 X1) = (k X1 (M.op (σ y) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq28236 eq12
    | (have j0 := eq12 X1 (M.op (σ y) (σ y))
       grind)
    | exact resolve eq12 eq28236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28609 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ y) (M.op X0 (M.op (σ y) (σ y)))) ∨ (M.op X1 (M.op (σ y) (σ y))) = (k X1 (M.op (σ y) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq28236 eq13
    | (have j0 := eq13 X1 (M.op (σ y) (σ y))
       grind)
    | exact resolve eq13 eq28236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28236
  have eq28693 : ∀ X1 : G, (M.op X1 X1) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (M.op X1 (M.op (σ y) (σ y))) = (k X1 (M.op (σ y) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq28609 x X1
       have i₂ := eq51 x sF3 sF3 sF3
       grind)
    | exact superpose eq51 eq28609
    | (have j0 := eq28609 x X1
       grind)
    | exact resolve eq28609 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28609
  have eq28695 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (M.op X1 X1) = (M.op (σ y) (M.op X0 (M.op (σ y) (σ y)))) ∨ (M.op X1 X1) = (k X1 (M.op (σ y) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq28607 X0 X1
       have i₂ := eq51 X0 sF3 sF3 sF3
       grind)
    | exact superpose eq51 eq28607
    | (have j0 := eq28607 X0 X1
       grind)
    | exact resolve eq28607 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28607
  have eq28863 : ∀ X1 : G, (M.op X1 X1) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op X1 (M.op (σ y) (σ y))) = (k X1 (M.op (σ y) (σ y))) := by
    intro X1
    first
    | exact superpose eq545 eq28693
    | (have j0 := eq28693 X1
       grind)
    | exact resolve eq28693 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28693
  have eq28865 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ y) (M.op X0 (M.op (σ y) (σ y)))) ∨ (M.op X1 X1) = (k X1 (M.op (σ y) (σ y))) := by
    intro X0 X1
    first
    | (have j0 := eq28695 X0 X1
       grind)
    | (have r₁ := eq28695 X0 X1
       have r₂ := eq10169 (σ y) (σ y)
       grind)
    | exact resolve eq28695 eq10169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28695
  have eq28959 : ∀ X1 : G, (M.op X1 X1) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X1 (M.op (σ y) (σ y))) = (k X1 (M.op (σ y) (σ y))) := by
    intro X1
    first
    | exact superpose eq3001 eq28863
    | (have j0 := eq28863 X1
       grind)
    | (have r₁ := eq28863 (σ (M.op x y))
       have r₂ := eq3001
       grind)
    | exact resolve eq28863 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28863
  have eq28961 : ∀ X1 : G, (M.op X1 X1) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (M.op X1 X1) = (k X1 (M.op (σ y) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq28865 x X1
       have i₂ := eq51 x sF3 sF3 sF3
       grind)
    | exact superpose eq51 eq28865
    | (have j0 := eq28865 x X1
       grind)
    | exact resolve eq28865 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq28865
  have eq29008 : ∀ X1 : G, (M.op X1 X1) ≠ (σ y) ∨ (M.op X1 (M.op (σ y) (σ y))) = (k X1 (M.op (σ y) (σ y))) := by
    intro X1
    first
    | exact superpose eq6786 eq28959
    | (have j0 := eq28959 X1
       grind)
    | exact resolve eq28959 eq6786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28959
  have eq29010 : ∀ X1 : G, (M.op X1 X1) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op X1 X1) = (k X1 (M.op (σ y) (σ y))) := by
    intro X1
    first
    | exact superpose eq545 eq28961
    | (have j0 := eq28961 X1
       grind)
    | exact resolve eq28961 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq28961
  have eq29030 : ∀ X1 : G, (M.op X1 X1) ≠ (σ y) ∨ (M.op X1 (σ y)) = (k X1 (σ y)) := by
    intro X1
    first
    | exact superpose eq6681 eq29008
    | (have j0 := eq29008 X1
       grind)
    | (have r₁ := eq29008 (σ y)
       have r₂ := eq6681
       grind)
    | exact resolve eq29008 eq6681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29008
  have eq29032 : ∀ X1 : G, (M.op X1 X1) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X1 X1) = (k X1 (M.op (σ y) (σ y))) := by
    intro X1
    first
    | exact superpose eq3001 eq29010
    | (have j0 := eq29010 X1
       grind)
    | exact resolve eq29010 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29010
  have eq29047 : ∀ X1 : G, (M.op X1 X1) = (σ y) ∨ (M.op X1 X1) = (k X1 (M.op (σ y) (σ y))) := by
    intro X1
    first
    | exact superpose eq6786 eq29032
    | (have j0 := eq29032 X1
       grind)
    | exact resolve eq29032 eq6786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29032
  have eq29053 : ∀ X1 : G, (M.op X1 X1) = (k X1 (σ y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X1
    first
    | exact superpose eq6681 eq29047
    | (have j0 := eq29047 X1
       grind)
    | exact resolve eq29047 eq6681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29047
  have eq29439 : ∀ X0 : G, y ≠ (k X0 y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq28228 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28228
  have eq29762 : ∀ X0 : G, y ≠ (τ (k X0 (σ y))) ∨ y = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29439 (τ X0)
       have i₂ := eq3075 X0
       grind)
    | exact superpose eq3075 eq29439
    | (have j0 := eq29439 (τ X0)
       grind)
    | exact resolve eq29439 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29439
  have eq30049 : ∀ X0 : G, (σ y) ≠ (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq477 eq29030
    | (have j0 := eq29030 (M.op X0 (σ y))
       grind)
    | exact resolve eq29030 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq30068 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2003 eq29030
    | (have j0 := eq29030 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq29030 eq2003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003 eq29030
  have eq30072 : (σ y) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq3001 eq30068
    | exact resolve eq30068 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30068
  have eq30089 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq1888 eq30049
    | (have j0 := eq30049 X0
       grind)
    | exact resolve eq30049 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888 eq30049
  have eq30105 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have r₁ := eq30072
       have r₂ := eq6786
       grind)
    | exact resolve eq30072 eq6786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30072
  have eq30116 : ∀ X0 : G, (σ y) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq3001 eq30089
    | (have j0 := eq30089 X0
       grind)
    | exact resolve eq30089 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001 eq30089
  have eq30128 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq7640 eq30105
    | exact resolve eq30105 eq7640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7640 eq30105
  have eq30134 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq30116 X0
       grind)
    | (have r₁ := eq30116 X0
       have r₂ := eq6786
       grind)
    | exact resolve eq30116 eq6786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30116
  have eq30146 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq10169 eq30134
    | exact resolve eq30134 eq10169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10169 eq30134
  have eq30155 : ∀ X0 : G, (σ y) = (k (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq6681 eq30146
    | exact resolve eq30146 eq6681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6681 eq30146
  have eq31117 : ∀ X0 : G, (σ y) ≠ (k X0 (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq29053 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29053
  have eq37359 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq7371
    | exact resolve eq7371 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq7371
  have eq37410 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37359
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37359
    | exact resolve eq37359 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37359
  have eq37428 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq37410
    | exact resolve eq37410 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37410
  have eq37481 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37428 eq82
    | (have j0 := eq82 x (σ (M.op x y))
       grind)
    | exact resolve eq82 eq37428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq37482 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6786 eq37481
    | exact resolve eq37481 eq6786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6786 eq37481
  have eq57111 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq45 eq12260
    | exact resolve eq12260 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq12260
  have eq57578 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37428 eq57111
    | exact resolve eq57111 eq37428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37428 eq57111
  have eq76390 : y ≠ (τ (σ y)) ∨ y = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq30128 eq29762
    | (have j0 := eq29762 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq29762 eq30128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29762 eq30128
  have eq76404 : y = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have r₁ := eq76390
       have r₂ := eq29
       grind)
    | exact resolve eq76390 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76390
  have eq76446 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 (τ (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq76404 eq57
    | exact resolve eq57 eq76404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq76404
  have eq275238 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (σ y)))) = (σ (M.op (τ X0) (σ y))) ∨ (σ y) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq6806 eq7381
    | (have j0 := eq7381 X0 X1
       grind)
    | exact resolve eq7381 eq6806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6806 eq7381
  have eq358350 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (σ y)))) = (σ (M.op (τ X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq275238
    | (have j0 := eq275238 X0 (σ x)
       grind)
    | exact resolve eq275238 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275238
  have eq408900 : ∀ X0 : G, (M.op (τ X0) (σ y)) = (τ (k X0 (σ (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq358350 eq16
    | exact resolve eq16 eq358350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358350
  have eq408980 : ∀ X0 : G, (M.op (τ X0) (σ y)) = (k (τ X0) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq408900 X0
       have i₂ := eq348 X0 sF4
       grind)
    | exact superpose eq348 eq408900
    | exact resolve eq408900 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq408900
  have eq409119 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq408980 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq408980
    | exact resolve eq408980 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408980
  have eq409280 : ∀ X0 : G, (τ (M.op (σ X0) (σ y))) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq409119 eq388
    | exact resolve eq388 eq409119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq409119
  have eq628533 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq409280 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq409280
    | (have j0 := eq409280 x
       grind)
    | exact resolve eq409280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628598 : ∀ X0 : G, (τ (k (M.op (σ X0) (σ y)) (σ y))) = (k (k X0 (τ (M.op (σ x) (σ y)))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq409280 eq3075
    | exact resolve eq3075 eq409280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq628615 : ∀ X0 : G, (τ (σ y)) = (k (k X0 (τ (M.op (σ x) (σ y)))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30155 eq628598
    | exact resolve eq628598 eq30155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30155 eq628598
  have eq628632 : (τ (M.op (σ x) (σ y))) = (τ (k (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq628533
       have i₂ := eq265 sF4
       grind)
    | exact superpose eq265 eq628533
    | exact resolve eq628533 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628533
  have eq628672 : ∀ X0 : G, y = (k (k X0 (τ (M.op (σ x) (σ y)))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29 eq628615
    | exact resolve eq628615 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628615
  have eq628681 : (τ (M.op (σ x) (σ y))) = (τ (k (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq628632
    | exact resolve eq628632 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628632
  have eq642017 : ∀ X0 : G, (σ y) = (k (k X0 (σ (τ (M.op (σ x) (σ y))))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq628672 eq353
    | exact resolve eq353 eq628672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq628672
  have eq642054 : ∀ X0 : G, (σ y) = (k (k X0 (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq642017 X0
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq642017
    | exact resolve eq642017 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642017
  have eq642070 : ∀ X0 : G, (σ y) = (k (k X0 (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq642054 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq642054
    | (have j0 := eq642054 X0
       grind)
    | exact resolve eq642054 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642054
  have eq1326108 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq57578
    | (have j0 := eq57578 (σ x)
       grind)
    | exact resolve eq57578 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57578
  have eq1328621 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1326108 eq37482
    | exact resolve eq37482 eq1326108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37482 eq1326108
  have eq1328957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1328621
  have eq1329160 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1328957
       have r₂ := eq27
       grind)
    | exact resolve eq1328957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328957
  have eq1329572 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1329160 eq29
    | exact resolve eq29 eq1329160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1329160
  have eq1330055 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq1329572
    | exact resolve eq1329572 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329572
  have eq1330056 : y = (M.op x y) := by grind
  clear eq1330055
  have eq1330088 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1330056 eq20
    | exact resolve eq20 eq1330056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1330309 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1330088
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1330088
    | exact resolve eq1330088 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330088
  have eq1330317 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1330309 eq26
    | exact resolve eq26 eq1330309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1330413 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1330309 eq31117
    | exact resolve eq31117 eq1330309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31117
  have eq1330632 : ∀ X0 : G, (τ (M.op (σ X0) (σ (M.op x y)))) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1330309 eq409280
    | exact resolve eq409280 eq1330309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409280
  have eq1330654 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1330309 eq642070
    | exact resolve eq642070 eq1330309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642070
  have eq1330702 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq1330654 X0
       grind)
    | (have r₁ := eq1330654 X0
       have r₂ := eq27
       grind)
    | exact resolve eq1330654 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330654
  have eq1330714 : ∀ X0 : G, (τ (M.op (σ X0) (σ (M.op x y)))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq1330632 X0
       grind)
    | (have r₁ := eq1330632 X0
       have r₂ := eq27
       grind)
    | exact resolve eq1330632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330632
  have eq1455703 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (k X0 (M.op (σ x) (σ y))) (k X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1330702 eq1330413
    | (have j0 := eq1330413 (k X0 (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq1330413 (k X0 (M.op (σ x) (σ y)))
       have r₂ := eq1330702 X0
       grind)
    | exact resolve eq1330413 eq1330702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330413 eq1330702
  have eq1455725 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k X0 (M.op (σ x) (σ y))) (k X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq1455703 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455703
  have eq1471107 : (τ (M.op (σ x) (σ (M.op x y)))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1330714 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1330714
    | (have j0 := eq1330714 x
       grind)
    | exact resolve eq1330714 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1330714
  have eq1471214 : (τ (M.op (σ x) (σ (M.op x y)))) = (τ (k (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1471107
       have i₂ := eq265 sF4
       grind)
    | exact superpose eq265 eq1471107
    | exact resolve eq1471107 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq1471107
  have eq1471268 : (τ (M.op (σ x) (σ y))) = (τ (k (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1330317 eq1471214
    | exact resolve eq1471214 eq1330317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330317 eq1471214
  have eq1471358 : (σ (τ (M.op (σ x) (σ y)))) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1471268 eq15
    | exact resolve eq15 eq1471268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471268
  have eq1471420 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1471358
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1471358
    | exact resolve eq1471358 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471358
  have eq1954192 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq262 X0
       have i₂ := eq3175 X0
       grind)
    | exact superpose eq3175 eq262
    | (have j0 := eq262 X0
       grind)
    | exact resolve eq262 eq3175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq3175
  have eq1954250 : (k (σ x) (k (σ x) (M.op (σ x) (σ y)))) = (σ (M.op x (τ (M.op (σ x) (σ y))))) ∨ (τ (M.op (σ x) (σ y))) = (τ (M.op (k (σ x) (M.op (σ x) (σ y))) (k (σ x) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq628681 eq1954192
    | exact resolve eq1954192 eq628681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628681 eq1954192
  have eq1954478 : (k (σ x) (M.op (σ x) (σ y))) = (σ (M.op x (τ (M.op (σ x) (σ y))))) ∨ (τ (M.op (σ x) (σ y))) = (τ (M.op (k (σ x) (M.op (σ x) (σ y))) (k (σ x) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1471420 eq1954250
    | exact resolve eq1954250 eq1471420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954250
  have eq1954519 : (M.op (σ x) (σ y)) = (σ (M.op x (τ (M.op (σ x) (σ y))))) ∨ (τ (M.op (σ x) (σ y))) = (τ (M.op (k (σ x) (M.op (σ x) (σ y))) (k (σ x) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1471420 eq1954478
    | exact resolve eq1954478 eq1471420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471420 eq1954478
  have eq1954553 : (τ (σ (M.op x y))) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x (τ (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1455725 eq1954519
    | exact resolve eq1954519 eq1455725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455725 eq1954519
  have eq1954579 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x (τ (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq1954553
    | exact resolve eq1954553 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1954553
  have eq1954600 : y = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x (τ (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1330056 eq1954579
    | exact resolve eq1954579 eq1330056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954579
  have eq1954621 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1330309 eq1954600
    | exact resolve eq1954600 eq1330309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954600
  have eq1954639 : (M.op (σ x) (σ y)) = (σ (M.op x (τ (M.op (σ x) (σ y))))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1954621
       have r₂ := eq27
       grind)
    | exact resolve eq1954621 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954621
  have eq1954689 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1954639 eq16
    | exact resolve eq16 eq1954639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954639
  have eq1955358 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1954689 eq76446
    | exact resolve eq76446 eq1954689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76446
  have eq1966741 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1955358 eq1954689
    | exact resolve eq1954689 eq1955358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954689 eq1955358
  have eq1966875 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1966741
  have eq1966960 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1966875
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1966875
    | exact resolve eq1966875 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1966875
  have eq1967585 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1330056 eq1966960
    | exact resolve eq1966960 eq1330056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330056 eq1966960
  have eq1967586 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1967585
  have eq1969307 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1967586 eq15
    | exact resolve eq15 eq1967586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967586
  have eq1969400 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1969307
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1969307
    | exact resolve eq1969307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1969307
  have eq1969452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1330309 eq1969400
    | exact resolve eq1969400 eq1330309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330309 eq1969400
  have eq1969488 : False := by grind
  exact eq1969488

/-- `Equation4542`: `x ◇ (y ◇ z) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_y_pyx_Equation4542 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4542 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4542.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X2) := by
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
  clear eq43
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
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X3 X0)) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X3 X0)
       have i₂ := eq14 X1 X3 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 X0) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X3))) = (M.op (M.op X3 (M.op (M.op X2 X3) X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X3) X0) X2 X3
       have i₂ := eq14 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X1)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X0) X3 X1
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X2 X0))) = (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X2 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op (M.op x y) x) := by
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
  have eq62 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ X1 ∨ (M.op X2 X0) = (k (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X2 X0) X1
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X2 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X2 X0) ∨ (k X2 (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X2 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X2 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X3 X0)) = (M.op (M.op X0 X2) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq56 X0 x X2 X3
       have i₂ := eq14 X2 (M.op X0 x) X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq75 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X2 X0) ∨ (M.op X2 (M.op X2 X0)) = X2 ∨ (k (M.op X2 X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 X0) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X2 X0) X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq77 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq84 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq16
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq83
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq16
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq247 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
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
  clear eq42
  have eq270 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq382 : (k y (k y x)) = (τ (k (σ y) (k (σ y) (σ x)))) := by
    first
    | exact superpose eq90 eq270
    | exact resolve eq270 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq401 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq63
    | (have j0 := eq63 X0 X1 y x
       grind)
    | exact resolve eq63 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq63
    | (have j0 := eq63 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq63 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op X4 X0)) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X3 X2) X4 X0
       have i₂ := eq63 X0 X3 X2 X1
       grind)
    | (have i₁ := eq14 (M.op X3 X2) X4 X0
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq14
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x y)) = (M.op X2 (M.op X0 (M.op X1 y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq401 X2 (M.op y X0)
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq401
    | exact resolve eq401 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq401 X0 x
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq401
    | (have j1 := eq14 X0 x y
       grind)
    | exact resolve eq401 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X2 : G, (M.op X2 (M.op x y)) = (M.op X2 (M.op X0 (M.op x y))) := by
    intro X0 X2
    first
    | (have i₁ := eq443 X0 x X2
       have i₂ := eq401 X0 x
       grind)
    | (have i₁ := eq443 X0 x X2
       have i₂ := eq401 X0 x
       grind)
    | exact superpose eq401 eq443
    | (have j0 := eq443 X0 x X2
       grind)
    | exact resolve eq443 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq464 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op X2 (M.op X0 (M.op X1 (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq403 X0 (M.op sF3 X0)
       have i₂ := eq14 X0 X1 sF3
       grind)
    | exact superpose eq14 eq403
    | exact resolve eq403 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq403 X0 x
       have i₂ := eq14 X0 x sF3
       grind)
    | exact superpose eq14 eq403
    | (have j1 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq403 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op X2 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X2
    first
    | exact superpose eq403 eq464
    | (have j0 := eq464 X0 (σ x) X2
       grind)
    | exact resolve eq464 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq485 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X3 X2) (M.op X4 (M.op X5 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq57 X4 X5 X0 (M.op X3 X2)
       have i₂ := eq63 X0 X3 X2 X1
       grind)
    | (have i₁ := eq57 X4 X5 X0 (M.op X3 X2)
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq57
    | exact resolve eq57 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 X4 (M.op X2 X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X5 X3) X5) X3) = (M.op (M.op X4 X5) (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq59 X5 X3 X4 (M.op X3 X0)
       have i₂ := eq57 X1 X2 X3 X0
       grind)
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op (M.op X1 y) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59
    | (have j0 := eq59 X1 y X0 x
       grind)
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op (M.op X2 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X2 X0 X1 x
       have i₂ := eq14 (M.op X1 X2) x X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq67 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq67
    | (have j0 := eq67 y X0 x
       grind)
    | exact resolve eq67 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq67
    | (have j0 := eq67 (σ y) X0 (σ x)
       grind)
    | exact resolve eq67 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 X0 x
       have i₂ := eq59 X0 X1 (M.op x X1) x
       grind)
    | exact superpose eq59 eq67
    | exact resolve eq67 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq467 eq988
    | exact resolve eq988 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1043 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq986 X0
       have i₂ := eq446 X0
       grind)
    | exact superpose eq446 eq986
    | exact resolve eq986 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1094 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq403 eq1041
    | exact resolve eq1041 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1041 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       have r₂ := eq1041 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1041 eq1094
    | exact resolve eq1094 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1124 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1043 (M.op x y)
       have i₂ := eq401 sF0 x
       grind)
    | (have i₁ := eq1043 (M.op x y)
       have i₂ := eq401 sF0 x
       grind)
    | exact superpose eq401 eq1043
    | exact resolve eq1043 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1134 : ∀ X0 : G, (M.op X0 (M.op x y)) ≠ (M.op (M.op x y) X0) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq1043 eq13
    | (have j0 := eq13 (M.op x y) (M.op (M.op x y) X0)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op (M.op x y) (M.op x y))
       have r₂ := eq1043 (M.op x y)
       grind)
    | exact resolve eq13 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1043 eq1124
    | exact resolve eq1124 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1155 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1041 eq1115
    | exact resolve eq1115 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1284 : ∀ X0 : G, (M.op (σ y) X0) ≠ (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq66
    | (have j0 := eq66 X0 (σ x) (σ y)
       grind)
    | exact resolve eq66 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1469 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) y) = (M.op x (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 x X0 X1 y
       have i₂ := eq61 (M.op X1 y)
       grind)
    | exact superpose eq61 eq58
    | exact resolve eq58 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1611 : (M.op (M.op (M.op x y) x) y) = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq1469 x x
       have i₂ := eq57 x x y x
       grind)
    | exact superpose eq57 eq1469
    | exact resolve eq1469 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1687 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq1611
       have i₂ := eq446 x
       grind)
    | exact superpose eq446 eq1611
    | exact resolve eq1611 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1825 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 (M.op (M.op x y) x))) = (M.op (M.op (M.op X1 x) (M.op X2 y)) (M.op (M.op x y) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 (M.op X0 x) X1 y x
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq60
    | exact resolve eq60 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1828 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x)))) = (M.op (M.op (M.op X1 (σ x)) (M.op X2 (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq62 eq60
    | exact resolve eq60 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1880 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X2 X0)) (M.op x y)) = (M.op X0 (M.op X1 (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq463 X2 (M.op sF0 (M.op X1 X2))
       have i₂ := eq60 sF0 X1 X2 x
       grind)
    | exact superpose eq60 eq463
    | exact resolve eq463 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1905 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op (M.op (M.op x y) (M.op X2 X0)) (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq1880 x X0 X2
       have i₂ := eq57 X0 x sF0 x
       grind)
    | exact superpose eq57 eq1880
    | exact resolve eq1880 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880
  have eq1931 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x)))) = (M.op (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq403 eq1828
    | (have j0 := eq1828 X0 X1 (σ x)
       grind)
    | exact resolve eq1828 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1934 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op (M.op x y) x))) = (M.op (M.op (M.op X1 x) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1825 X0 X1 x
       have i₂ := eq401 (M.op X1 x) x
       grind)
    | (have i₁ := eq1825 X0 X1 x
       have i₂ := eq401 (M.op X1 x) X1
       grind)
    | exact superpose eq401 eq1825
    | (have j0 := eq1825 X0 X1 x
       grind)
    | exact resolve eq1825 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq1984 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op (M.op X2 X0) (M.op x y)) := by
    intro X0 X2
    first
    | exact superpose eq1043 eq1905
    | exact resolve eq1905 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq1996 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x)))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1931 X0 x
       have i₂ := eq59 sF4 sF2 (M.op x sF2) sF4
       grind)
    | exact superpose eq59 eq1931
    | exact resolve eq1931 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq1998 : ∀ X0 : G, (M.op y (M.op X0 (M.op (M.op x y) x))) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq1934 X0 x
       have i₂ := eq59 sF0 x (M.op x x) sF0
       grind)
    | exact superpose eq59 eq1934
    | exact resolve eq1934 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934
  have eq2034 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op (M.op X2 X0) (M.op x y)) := by
    intro X0 X2
    first
    | exact superpose eq1043 eq1984
    | exact resolve eq1984 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1984
  have eq2040 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x)))) := by
    intro X0
    first
    | exact superpose eq1041 eq1996
    | exact resolve eq1996 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq1996
  have eq2042 : ∀ X0 : G, (M.op (M.op x (M.op x y)) x) = (M.op y (M.op X0 (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq1043 eq1998
    | exact resolve eq1998 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998
  have eq2068 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq2040 x
       have i₂ := eq57 x sF4 sF2 sF3
       grind)
    | exact superpose eq57 eq2040
    | exact resolve eq2040 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2070 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq2042 x
       have i₂ := eq57 x sF0 x y
       grind)
    | exact superpose eq57 eq2042
    | exact resolve eq2042 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042
  have eq2078 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq2068
    | exact resolve eq2068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2080 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq2070
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2070
    | exact resolve eq2070 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq2191 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq2078
       have i₂ := eq14 sF4 x sF2
       grind)
    | exact superpose eq14 eq2078
    | exact resolve eq2078 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2231 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq2080
       have i₂ := eq14 sF0 x x
       grind)
    | exact superpose eq14 eq2080
    | exact resolve eq2080 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2414 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X2 (M.op X2 (M.op X3 X0))) ∨ (M.op X2 (M.op X2 (M.op X2 (M.op X3 X0)))) = X2 ∨ (k (M.op X2 (M.op X2 (M.op X3 X0))) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75 (M.op X2 (M.op X3 X0)) X0 X2
       have i₂ := eq60 X2 X3 X0 X1
       grind)
    | exact superpose eq60 eq75
    | (have j0 := eq75 (M.op X2 (M.op X3 X0)) X1 X2
       grind)
    | (have r₁ := eq75 (M.op X3 (M.op X3 X3)) X3 X3
       have r₂ := eq60 X3 X3 X3 X3
       grind)
    | exact resolve eq75 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq75
  have eq2555 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1043 eq1149
    | exact resolve eq1149 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043 eq1149
  have eq2628 : (M.op x y) ≠ (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2555 eq13
    | (have j0 := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq13 eq2555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2688 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2689 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2707 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq91 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2708 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq2709 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707
  have eq2710 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2688 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688
  have eq2711 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2689 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2689 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2689 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq2689 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689
  have eq2712 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2710 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2710 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2710 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq2710 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710
  have eq2721 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2711 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq2711
    | (have j0 := eq2711 X0 X1
       grind)
    | exact resolve eq2711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2722 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2712 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq2712
    | (have j0 := eq2712 X0 X1
       grind)
    | exact resolve eq2712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2712
  have eq2938 : ∀ X0 : G, (k (k y x) (τ X0)) = (τ (k (k (σ y) (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq349 (k y x) X0
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq349
    | exact resolve eq349 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq3741 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op X1 y) X1) y) := by
    intro X1
    first
    | exact superpose eq2034 eq749
    | exact resolve eq749 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq3775 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op X0 (M.op x y)) (M.op (M.op X0 y) X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0 y (M.op X0 y)
       have i₂ := eq3741 X0
       grind)
    | exact superpose eq3741 eq67
    | exact resolve eq67 eq3741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3741
  have eq3824 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq3775 x
       have i₂ := eq59 sF0 x x (M.op x y)
       grind)
    | exact superpose eq59 eq3775
    | exact resolve eq3775 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq3775
  have eq3865 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) X0) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq2034 eq3824
    | exact resolve eq3824 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3824
  have eq5198 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq1115 eq1284
    | (have j0 := eq1284 (M.op X0 (σ y))
       grind)
    | exact resolve eq1284 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq1284
  have eq5209 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq1155 eq5198
    | (have j0 := eq5198 X0
       grind)
    | (have r₁ := eq5198 (σ x)
       have r₂ := eq1155
       grind)
    | exact resolve eq5198 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5198
  have eq5215 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have j0 := eq5209 X0
       grind)
    | (have r₁ := eq5209 (σ x)
       have r₂ := eq403 (σ y) (σ x)
       grind)
    | (have r₁ := eq5209 x
       have r₂ := eq403 (σ y) x
       grind)
    | exact resolve eq5209 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5209
  have eq5220 : (σ y) = (k (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq403 eq5215
    | (have j0 := eq5215 (σ x)
       grind)
    | exact resolve eq5215 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5215
  have eq5340 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op X1 y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3865 x
       have i₂ := eq14 sF0 X1 x
       grind)
    | exact superpose eq14 eq3865
    | exact resolve eq3865 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865
  have eq9549 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq758 X0 X1 X2
       have i₂ := eq990 X2 X0
       grind)
    | exact superpose eq990 eq758
    | exact resolve eq758 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq10120 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op x y) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5340 X2 X1
       have i₂ := eq14 y X0 X1
       grind)
    | exact superpose eq14 eq5340
    | exact resolve eq5340 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5340
  have eq18977 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2709 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq2709
    | (have j0 := eq2709 (τ X0)
       grind)
    | exact resolve eq2709 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq18985 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18977 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq18977
    | (have j0 := eq18977 X0
       grind)
    | exact resolve eq18977 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18977
  have eq18991 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18985 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq18985
    | (have j0 := eq18985 X0
       grind)
    | exact resolve eq18985 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18985
  have eq19514 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X3 X2) (M.op X4 (M.op X5 X0))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq485 X0 x X2 X3 X4 X5
       have i₂ := eq9549 X0 x X2
       grind)
    | exact superpose eq9549 eq485
    | exact resolve eq485 eq9549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq19688 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq26 eq19514
    | (have j0 := eq19514 X0 (σ y) (σ x) X1 X2
       grind)
    | exact resolve eq19514 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19514
  have eq24001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq24002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq24001
    | exact resolve eq24001 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24001
  have eq24013 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq24002
       have r₂ := eq27
       grind)
    | exact resolve eq24002 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24002
  have eq24015 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq24013
    | exact resolve eq24013 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24013
  have eq24026 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24015 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq24015
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq24015
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq24015
       grind)
    | exact resolve eq12 eq24015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24015
  have eq24074 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq24026
  have eq24094 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq24074
    | exact resolve eq24074 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24074
  have eq24095 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq24094
  have eq24272 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24095 eq90
    | exact resolve eq90 eq24095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24095
  have eq24291 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq28 eq24272
    | exact resolve eq24272 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24272
  have eq24527 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq24291
       grind)
    | exact superpose eq24291 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq24291
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq24291
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq24291
       grind)
    | exact resolve eq12 eq24291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24291
  have eq24575 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24527
  have eq24576 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24575
  have eq24596 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24576
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24576
    | exact resolve eq24576 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24576
  have eq24597 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24596
  have eq24609 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq24597
       grind)
    | exact superpose eq24597 eq83
    | exact resolve eq83 eq24597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24616 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq24597
       grind)
    | exact superpose eq24597 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq24597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24617 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24616
  have eq24619 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24617
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24617
    | exact resolve eq24617 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24617
  have eq24620 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24619
  have eq24627 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24609
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24609
    | exact resolve eq24609 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24609
  have eq24636 : (M.op (M.op x y) x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2231 y
       have i₂ := eq24620
       grind)
    | exact superpose eq24620 eq2231
    | exact resolve eq2231 eq24620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24637 : (M.op (M.op x y) x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61 y
       have i₂ := eq24620
       grind)
    | exact superpose eq24620 eq61
    | exact resolve eq61 eq24620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24648 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 y x X1
       have i₂ := eq24620
       grind)
    | exact superpose eq24620 eq63
    | exact resolve eq63 eq24620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24652 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x X0) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq67 x x y
       have i₂ := eq24620
       grind)
    | exact superpose eq24620 eq67
    | exact resolve eq67 eq24620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq24659 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X1 (M.op X2 x)) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq427 X1 X2 x y X0
       have i₂ := eq24620
       grind)
    | exact superpose eq24620 eq427
    | exact resolve eq427 eq24620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24660 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op (M.op x (M.op X2 X1)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq427 x X2 X1 X0 y
       have i₂ := eq24620
       grind)
    | exact superpose eq24620 eq427
    | exact resolve eq427 eq24620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24620
  have eq24694 : ∀ X0 X1 : G, (M.op (M.op x X1) x) = (M.op (M.op X0 X1) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq24660 X0 X1 x
       have i₂ := eq9549 x x X1
       grind)
    | exact superpose eq9549 eq24660
    | exact resolve eq24660 eq9549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24660
  have eq24695 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X1 x) X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq24659 X0 X1 x
       have i₂ := eq9549 X1 x x
       grind)
    | exact superpose eq9549 eq24659
    | exact resolve eq24659 eq9549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24659
  have eq24699 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24652 X0
       have i₂ := eq446 X0
       grind)
    | exact superpose eq446 eq24652
    | exact resolve eq24652 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24652
  have eq24724 : (k y (k y x)) = (τ (k (σ y) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24627 eq382
    | exact resolve eq382 eq24627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq24729 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24627 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq24627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24730 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24729
  have eq24734 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24730
    | exact resolve eq24730 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24730
  have eq24735 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24734
  have eq24740 : (k y x) = (k y (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90 eq24724
    | exact resolve eq24724 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24724
  have eq24754 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24735 eq62
    | exact resolve eq62 eq24735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24765 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq24735 eq63
    | exact resolve eq63 eq24735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24777 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op (σ x) (M.op X2 X1)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq24735 eq427
    | exact resolve eq427 eq24735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq24793 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op X0 (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24735 eq9549
    | exact resolve eq9549 eq24735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24735
  have eq24811 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (σ x)) = (M.op (M.op X0 X1) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq24777 X0 x X1
       have i₂ := eq9549 sF2 X1 x
       grind)
    | exact superpose eq9549 eq24777
    | exact resolve eq24777 eq9549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24777
  have eq25084 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24636 eq10120
    | exact resolve eq10120 eq24636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10120
  have eq25097 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op y (M.op X0 y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2231 eq25084
    | exact resolve eq25084 eq2231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25084
  have eq25137 : (M.op (M.op x y) x) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25097 x
       have i₂ := eq401 y x
       grind)
    | (have i₁ := eq25097 x
       have i₂ := eq401 y x
       grind)
    | exact superpose eq401 eq25097
    | (have j0 := eq25097 x
       grind)
    | exact resolve eq25097 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25097
  have eq26915 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24637 eq24648
    | exact resolve eq24648 eq24637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24637
  have eq26920 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24648 X0 x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq24648
    | exact resolve eq24648 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27097 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq26915 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26915
  have eq27220 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq27097 X0
       have i₂ := eq401 X0 y
       grind)
    | exact superpose eq401 eq27097
    | exact resolve eq27097 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27097
  have eq27340 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op X1 X0) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq2034 eq27220
    | exact resolve eq27220 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27355 : (M.op (M.op x y) y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2555 eq27220
    | exact resolve eq27220 eq2555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29506 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24699 (M.op X0 x)
       have i₂ := eq24648 x X0
       grind)
    | exact superpose eq24648 eq24699
    | exact resolve eq24699 eq24648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29610 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29506 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29506
  have eq29688 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2034 eq29610
    | exact resolve eq29610 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29610
  have eq29749 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29688
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29688
    | exact resolve eq29688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29688
  have eq29803 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29749 eq1687
    | exact resolve eq1687 eq29749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687 eq29749
  have eq30484 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24754 eq24765
    | exact resolve eq24765 eq24754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24754
  have eq30489 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24765 X0 x
       have i₂ := eq14 X0 x sF2
       grind)
    | exact superpose eq14 eq24765
    | exact resolve eq24765 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30668 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq30484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30484
  have eq30792 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq403 eq30668
    | exact resolve eq30668 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq30668
  have eq38505 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X5) X3) = (M.op (M.op X4 X5) (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq743 X0 X1 X2 X3 X4 X5
       have i₂ := eq990 X5 X3
       grind)
    | exact superpose eq990 eq743
    | exact resolve eq743 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq990
  have eq38758 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq26 eq38505
    | (have j0 := eq38505 X1 X2 X3 X0 (σ x) (σ y)
       grind)
    | exact resolve eq38505 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38505
  have eq40493 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26920 (M.op X0 x)
       have i₂ := eq24648 x X0
       grind)
    | exact superpose eq24648 eq26920
    | exact resolve eq26920 eq24648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24648
  have eq40618 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq40493 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40493
  have eq40695 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40618 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40618
    | (have j0 := eq40618 X0
       grind)
    | exact resolve eq40618 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40618
  have eq45915 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27220 eq29803
    | exact resolve eq29803 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29803
  have eq46006 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45915
  have eq46072 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46006
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq46006
    | exact resolve eq46006 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46006
  have eq46153 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46072 eq27355
    | exact resolve eq27355 eq46072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27355
  have eq46154 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46072 eq24636
    | exact resolve eq24636 eq46072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24636 eq46072
  have eq46223 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46154
  have eq46224 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46153
  have eq46649 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46224 eq2628
    | (have r₁ := eq2628
       have r₂ := eq46224
       grind)
    | exact resolve eq2628 eq46224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628 eq46224
  have eq46722 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46649
  have eq47916 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46722 eq2709
    | (have j0 := eq2709 (M.op x y)
       grind)
    | exact resolve eq2709 eq46722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709 eq46722
  have eq47919 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq47916
  have eq47923 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq47919
    | exact resolve eq47919 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47919
  have eq49681 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 (σ (M.op x y))) = (k (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq47923 eq65
    | (have j0 := eq65 (σ (M.op x y)) (σ (M.op x y)) X0
       grind)
    | exact resolve eq65 eq47923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq49733 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (k (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq49681 X0
       grind)
    | (have r₁ := eq49681 X0
       have r₂ := eq47923
       grind)
    | exact resolve eq49681 eq47923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47923 eq49681
  have eq51534 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ (k y x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2721 y (k y x)
       have i₂ := eq24740
       grind)
    | exact superpose eq24740 eq2721
    | (have j0 := eq2721 y x
       grind)
    | exact resolve eq2721 eq24740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24740
  have eq51652 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ (k y x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51534
  have eq51742 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ (k y x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51652
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq51652
    | exact resolve eq51652 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51652
  have eq51839 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ (k y x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51742
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51742
    | exact resolve eq51742 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51742
  have eq51934 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ (k y x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq51839
       have r₂ := eq51
       grind)
    | exact resolve eq51839 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51839
  have eq52029 : (σ y) = (M.op (σ y) (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51934
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq51934
    | exact resolve eq51934 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51934
  have eq52048 : (σ y) = (M.op (σ y) (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52029
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq52029
    | exact resolve eq52029 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52029
  have eq52361 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2722 y x
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq2722
    | (have j0 := eq2722 y x
       grind)
    | exact resolve eq2722 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722
  have eq52401 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq52361
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52361
    | exact resolve eq52361 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52361
  have eq52533 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq52401
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq52401
    | exact resolve eq52401 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52401
  have eq52646 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq52533
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq52533
    | exact resolve eq52533 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52533
  have eq52759 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq52646
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52646
    | exact resolve eq52646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52646
  have eq52859 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq52759
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq52759
    | exact resolve eq52759 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52759
  have eq53683 : (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52048 eq467
    | exact resolve eq467 eq52048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53685 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52048 eq13
    | (have j0 := eq13 (k (σ y) (σ x)) (σ y)
       grind)
    | (have r₁ := eq13 (k (σ y) (σ x)) (σ y)
       have r₂ := eq52048
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq52048
       grind)
    | exact resolve eq13 eq52048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52048
  have eq53747 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq53685
  have eq55405 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ y) X0) ∨ (σ y) = (M.op (σ y) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2708 (τ X0) y
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq2708
    | (have j0 := eq2708 (τ X0) y
       grind)
    | exact resolve eq2708 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq55487 : ∀ X0 : G, (k (σ y) X0) ≠ X0 ∨ (σ y) = (M.op (σ y) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55405 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq55405
    | (have j0 := eq55405 X0
       grind)
    | exact resolve eq55405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55405
  have eq55605 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (k (σ y) X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55487 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq55487
    | (have j0 := eq55487 X0
       grind)
    | exact resolve eq55487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55487
  have eq55720 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (k (σ y) X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55605 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55605
    | (have j0 := eq55605 X0
       grind)
    | exact resolve eq55605 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55605
  have eq55830 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ y)) ∨ (σ y) = (M.op (σ y) X0) ∨ (k (σ y) X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq55720 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55720
    | (have j0 := eq55720 X0
       grind)
    | exact resolve eq55720 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55720
  have eq55928 : ∀ X0 : G, (k (σ y) X0) ≠ X0 ∨ (σ y) = (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq55830 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq55830
    | (have j0 := eq55830 X0
       grind)
    | exact resolve eq55830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55830
  have eq68425 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X1 x))) = (M.op (M.op x (M.op (M.op x y) x)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 y X0 X1 x
       have i₂ := eq40695 X1
       grind)
    | exact superpose eq40695 eq58
    | exact resolve eq58 eq40695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq40695
  have eq68630 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X1 x))) = (M.op (M.op x x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq68425 X0 X1
       have i₂ := eq9549 x sF0 x
       grind)
    | exact superpose eq9549 eq68425
    | exact resolve eq68425 eq9549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9549 eq68425
  have eq68695 : (M.op (M.op x y) x) = (M.op (M.op x x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68630 x x
       have i₂ := eq57 x x x y
       grind)
    | exact superpose eq57 eq68630
    | exact resolve eq68630 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68630
  have eq68718 : (M.op (M.op x y) x) = (M.op (M.op x x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68695
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq68695
    | exact resolve eq68695 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68695
  have eq98578 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq68718
       have i₂ := eq14 x X0 x
       grind)
    | exact superpose eq14 eq68718
    | exact resolve eq68718 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68718
  have eq115251 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = X0 ∨ (k (M.op X0 (M.op X0 (M.op X0 X0))) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2414 X0 x X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414
  have eq115252 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (k (M.op X0 (M.op X0 (M.op X0 X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq115251 X0
       have i₂ := eq508 X0 X0 X0 X0 X0
       grind)
    | exact superpose eq508 eq115251
    | (have j0 := eq115251 X0
       grind)
    | exact resolve eq115251 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq115251
  have eq115785 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq115252 X0
       have i₂ := eq57 X0 X0 X0 X0
       grind)
    | exact superpose eq57 eq115252
    | (have j0 := eq115252 X0
       grind)
    | exact resolve eq115252 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq115252
  have eq126575 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24699 (M.op X0 x)
       have i₂ := eq98578 X0
       grind)
    | exact superpose eq98578 eq24699
    | exact resolve eq24699 eq98578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24699 eq98578
  have eq126725 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq126575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126575
  have eq126827 : (M.op x (M.op x y)) = (M.op (M.op (M.op x y) x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2034 eq126725
    | exact resolve eq126725 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126725
  have eq143944 : (M.op x (M.op x y)) = (M.op (M.op y (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25137 eq126827
    | exact resolve eq126827 eq25137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25137 eq126827
  have eq144110 : (M.op x (M.op x y)) = (M.op (M.op y (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq143944
  have eq180897 : ∀ X0 : G, (k x (τ X0)) = (τ (k (k (σ y) (σ x)) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2938 X0
       have i₂ := eq24597
       grind)
    | exact superpose eq24597 eq2938
    | exact resolve eq2938 eq24597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq181022 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (k (k (σ y) (σ x)) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq180897 X0
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq180897
    | exact resolve eq180897 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq180897
  have eq182649 : ∀ X0 : G, (σ (τ (k (σ x) X0))) = (k (k (σ y) (σ x)) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq181022 eq15
    | exact resolve eq15 eq181022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181022
  have eq182745 : ∀ X0 : G, (k (σ x) X0) = (k (k (σ y) (σ x)) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq182649 X0
       have i₂ := eq15 (k sF2 X0)
       grind)
    | exact superpose eq15 eq182649
    | exact resolve eq182649 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182649
  have eq183793 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X1) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq26920 X1
       have i₂ := eq24694 X0 X1
       grind)
    | exact superpose eq24694 eq26920
    | exact resolve eq26920 eq24694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184273 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X1) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq183793 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183793
  have eq236578 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X1)) = (M.op x (M.op X0 X1)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24695 X2 X1
       have i₂ := eq14 x X0 X1
       grind)
    | exact superpose eq14 eq24695
    | exact resolve eq24695 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24695
  have eq264276 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 X1) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq24811 eq30489
    | exact resolve eq30489 eq24811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264317 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24811 eq24793
    | exact resolve eq24793 eq24811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24793
  have eq264821 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq264317 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264317
  have eq264835 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 X1) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq264276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264276
  have eq268593 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30489 eq264835
    | exact resolve eq264835 eq30489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30489
  have eq269339 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq268593 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268593
  have eq269591 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq269339
    | (have j0 := eq269339 X0
       grind)
    | exact resolve eq269339 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269339
  have eq273019 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24811 eq269591
    | exact resolve eq269591 eq24811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269591
  have eq273404 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq273019 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273019
  have eq289015 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq273404 X0
       have i₂ := eq14 X0 X1 sF2
       grind)
    | exact superpose eq14 eq273404
    | exact resolve eq273404 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289042 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq273404 eq24811
    | exact resolve eq24811 eq273404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273404
  have eq289243 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq289042
  have eq289833 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq289243
       have i₂ := eq14 sF2 x sF2
       grind)
    | exact superpose eq14 eq289243
    | exact resolve eq289243 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289243
  have eq339281 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53683 eq24811
    | exact resolve eq24811 eq53683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24811 eq53683
  have eq339335 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq339281
  have eq339395 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq339335
       have r₂ := eq51
       grind)
    | exact resolve eq339335 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339335
  have eq339524 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq467 eq339395
    | exact resolve eq339395 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339395
  have eq339616 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2078 eq339524
    | exact resolve eq339524 eq2078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078 eq339524
  have eq340637 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq339616 eq24765
    | exact resolve eq24765 eq339616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24765
  have eq340666 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq339616 eq289015
    | exact resolve eq289015 eq339616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289015
  have eq340800 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq339616 eq264835
    | exact resolve eq264835 eq339616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339616
  have eq340801 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq340800
  have eq340817 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq340666 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340666
  have eq340845 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq340637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340637
  have eq340863 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq340801
       have r₂ := eq51
       grind)
    | exact resolve eq340801 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340801
  have eq340976 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq340817 X0
       grind)
    | (have r₁ := eq340817 X0
       have r₂ := eq51
       grind)
    | exact resolve eq340817 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340817
  have eq340995 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq340845 X0
       grind)
    | (have r₁ := eq340845 X0
       have r₂ := eq51
       grind)
    | exact resolve eq340845 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340845
  have eq341013 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq467 eq340863
    | exact resolve eq340863 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340863
  have eq341111 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq484 eq340976
    | exact resolve eq340976 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340976
  have eq341128 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq484 eq340995
    | exact resolve eq340995 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340995
  have eq341138 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1155 eq341013
    | exact resolve eq341013 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341013
  have eq341192 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq341138
    | exact resolve eq341138 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341138
  have eq341248 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq341192 eq5220
    | exact resolve eq5220 eq341192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5220 eq341192
  have eq370113 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq341128 eq341111
    | exact resolve eq341111 eq341128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341111 eq341128
  have eq370498 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq370113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370113
  have eq377194 : (k (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53747 eq182745
    | exact resolve eq182745 eq53747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53747 eq182745
  have eq377211 : (k (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq377194
  have eq377221 : (k (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq377211
       have r₂ := eq51
       grind)
    | exact resolve eq377211 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377211
  have eq394637 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264821 eq370498
    | exact resolve eq370498 eq264821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264821 eq370498
  have eq395258 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq394637
  have eq395736 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq395258
       have r₂ := eq51
       grind)
    | exact resolve eq395258 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395258
  have eq396355 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq395736
       have i₂ := eq14 sF2 x sF2
       grind)
    | exact superpose eq14 eq395736
    | exact resolve eq395736 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395736
  have eq397247 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) y) = (M.op (M.op X0 (σ x)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq396355 eq27340
    | exact resolve eq27340 eq396355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27340 eq396355
  have eq397286 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) y) = (M.op (M.op X0 (σ x)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq397247 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397247
  have eq397390 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) y) = (M.op (M.op X0 (σ x)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq397286 X0
       grind)
    | (have r₁ := eq397286 X0
       have r₂ := eq51
       grind)
    | exact resolve eq397286 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397286
  have eq397579 : (M.op (M.op (σ x) (σ y)) y) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2034 eq397390
    | exact resolve eq397390 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034 eq397390
  have eq398786 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op y (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq397579 eq236578
    | exact resolve eq236578 eq397579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236578 eq397579
  have eq398791 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op y (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq398786 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398786
  have eq398836 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op y (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq398791 X0
       grind)
    | (have r₁ := eq398791 X0
       have r₂ := eq51
       grind)
    | exact resolve eq398791 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398791
  have eq398966 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x (M.op X0 y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq463 eq398836
    | exact resolve eq398836 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq398836
  have eq399068 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq398966 x
       have i₂ := eq401 x x
       grind)
    | (have i₁ := eq398966 x
       have i₂ := eq401 x x
       grind)
    | exact superpose eq401 eq398966
    | (have j0 := eq398966 x
       grind)
    | exact resolve eq398966 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398966
  have eq399199 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq399068 eq144110
    | exact resolve eq144110 eq399068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144110 eq399068
  have eq399400 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq399199
  have eq399443 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq399400
       have r₂ := eq51
       grind)
    | exact resolve eq399400 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399400
  have eq399464 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2080 eq399443
    | exact resolve eq399443 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399443
  have eq400644 : (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq399464 eq1134
    | (have r₁ := eq1134 x
       have r₂ := eq399464
       grind)
    | exact resolve eq1134 eq399464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400827 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq399464 eq184273
    | exact resolve eq184273 eq399464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184273 eq399464
  have eq400838 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq400827
  have eq400885 : (M.op x y) = (k (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq400644
  have eq400913 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq400838
       have r₂ := eq51
       grind)
    | exact resolve eq400838 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400838
  have eq401073 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq400913
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq400913
    | exact resolve eq400913 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400913
  have eq405777 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27220 eq400885
    | exact resolve eq400885 eq27220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27220 eq400885
  have eq405796 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq405777
  have eq405810 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq405796
       have r₂ := eq51
       grind)
    | exact resolve eq405796 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405796
  have eq405823 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq405810
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq405810
    | exact resolve eq405810 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405810
  have eq405854 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq405823 eq90
    | exact resolve eq90 eq405823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405823
  have eq405929 : y = (k y x) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq405854
    | exact resolve eq405854 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405854
  have eq405934 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq405929
       have r₂ := eq50
       grind)
    | exact resolve eq405929 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405929
  have eq405961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k y x) := by
    first
    | exact superpose eq405934 eq2708
    | (have j0 := eq2708 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq2708 eq405934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2708 eq405934
  have eq405966 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k y x) := by grind
  clear eq405961
  have eq405967 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k y x) := by grind
  clear eq405966
  have eq405982 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k y x) := by
    first
    | exact superpose eq20 eq405967
    | exact resolve eq405967 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405967
  have eq453895 : (M.op x y) = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq401073 eq24694
    | exact resolve eq24694 eq401073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24694 eq401073
  have eq454137 : (M.op x y) = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq453895
  have eq454312 : (M.op x y) = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq454137
       have r₂ := eq51
       grind)
    | exact resolve eq454137 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454137
  have eq454419 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2080 eq454312
    | exact resolve eq454312 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080 eq454312
  have eq454638 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq454419 eq90
    | exact resolve eq90 eq454419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454419
  have eq454714 : y = (k y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq29 eq454638
    | exact resolve eq454638 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454638
  have eq454719 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq454714
       have r₂ := eq50
       grind)
    | exact resolve eq454714 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454714
  have eq472519 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24627 eq52859
    | (have r₁ := eq52859
       have r₂ := eq24627
       grind)
    | exact resolve eq52859 eq24627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24627 eq52859
  have eq472532 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq472519
  have eq472536 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq472532
       have r₂ := eq77
       grind)
    | exact resolve eq472532 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq472532
  have eq472545 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq472536 eq55
    | exact resolve eq55 eq472536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472635 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq472545
    | exact resolve eq472545 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472545
  have eq472693 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq472635 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq472635
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq472635
       grind)
    | exact resolve eq13 eq472635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472635
  have eq472854 : (σ x) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq472693
  have eq473086 : (τ (σ x)) = (k x y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq472854 eq55
    | exact resolve eq55 eq472854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq472854
  have eq473133 : y = (k x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq473086
    | exact resolve eq473086 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473086
  have eq473241 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq473133
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq473133
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq473133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473269 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq473133
       grind)
    | exact superpose eq473133 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq473133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473133
  have eq473288 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq473269
  have eq473307 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq473241
  have eq473323 : x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq473288
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq473288
       have r₂ := eq13 y x
       grind)
    | exact resolve eq473288 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473288
  have eq473334 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq473307
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq473307
    | exact resolve eq473307 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473307
  have eq473335 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq473334
  have eq473351 : x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq473323
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq473323
    | exact resolve eq473323 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473323
  have eq473352 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq473351
  have eq473413 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq473352
       grind)
    | exact superpose eq473352 eq44
    | exact resolve eq44 eq473352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq473352
  have eq473465 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq473413
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq473413
    | exact resolve eq473413 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473413
  have eq473524 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq473465 eq472536
    | exact resolve eq472536 eq473465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472536
  have eq473539 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq473524
  have eq474099 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq473539 eq2191
    | exact resolve eq2191 eq473539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191
  have eq475430 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq377221 eq55928
    | (have j0 := eq55928 (σ x)
       grind)
    | exact resolve eq55928 eq377221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55928 eq377221
  have eq475462 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq475430
       have r₂ := eq473465
       grind)
    | exact resolve eq475430 eq473465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473465 eq475430
  have eq475487 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq475462
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq475462
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq475462
       have r₂ := eq13 y x
       grind)
    | exact resolve eq475462 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475462
  have eq476082 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq473335
       grind)
    | exact superpose eq473335 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq473335
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq473335
       grind)
    | exact resolve eq12 eq473335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476232 : x ≠ y ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq473335
  have eq476244 : x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq476082
  have eq476370 : x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq476244
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq476244
    | exact resolve eq476244 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476244
  have eq476371 : x = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq476370
  have eq476483 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq475487 eq90
    | exact resolve eq90 eq475487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475487
  have eq476572 : y = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq29 eq476483
    | exact resolve eq476483 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476483
  have eq476578 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq476572
       have r₂ := eq50
       grind)
    | exact resolve eq476572 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476572
  have eq476580 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k y x) := by
    first
    | exact superpose eq476578 eq467
    | exact resolve eq467 eq476578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476587 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq476578 eq62
    | exact resolve eq62 eq476578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq476633 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq476578 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq476578
       grind)
    | exact resolve eq12 eq476578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476643 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ y = (k y x) := by
    intro X0 X1
    first
    | exact superpose eq476578 eq63
    | exact resolve eq63 eq476578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq476758 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ y)))) ∨ y = (k y x) := by
    intro X0 X1
    first
    | exact superpose eq476578 eq38758
    | exact resolve eq38758 eq476578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38758 eq476578
  have eq476785 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq476633
  have eq476799 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq19688 eq476758
    | exact resolve eq476758 eq19688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19688 eq476758
  have eq476874 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq26 eq476785
    | exact resolve eq476785 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476785
  have eq476900 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (k y x) := by
    first
    | exact superpose eq467 eq476799
    | exact resolve eq476799 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq476799
  have eq476957 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (k y x) := by
    first
    | exact superpose eq26 eq476900
    | exact resolve eq476900 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476900
  have eq478682 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (k y x) := by
    first
    | exact superpose eq476587 eq1102
    | exact resolve eq1102 eq476587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq476587
  have eq479049 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (k y x) := by
    first
    | (have r₁ := eq478682
       have r₂ := eq476580
       grind)
    | exact resolve eq478682 eq476580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478682
  have eq482470 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq476580 eq479049
    | exact resolve eq479049 eq476580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476580 eq479049
  have eq482493 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (k y x) := by grind
  clear eq482470
  have eq488613 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq115785 x
       have i₂ := eq26920 x
       grind)
    | exact superpose eq26920 eq115785
    | exact resolve eq115785 eq26920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26920
  have eq488757 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq49733 (M.op sF1 sF1)
       have i₂ := eq115785 sF1
       grind)
    | exact superpose eq115785 eq49733
    | (have j1 := eq115785 (σ (M.op x y))
       grind)
    | exact resolve eq49733 eq115785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49733 eq115785
  have eq488760 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq488757
  have eq488847 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq488613
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq488613
    | exact resolve eq488613 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488613
  have eq488993 : x = (M.op x y) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq488847
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq488847
    | exact resolve eq488847 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488847
  have eq488994 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq488993
  have eq489424 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq488994 eq2721
    | (have j0 := eq2721 (M.op x y) x
       grind)
    | exact resolve eq2721 eq488994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488994
  have eq489429 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq489424
  have eq489436 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq489429
    | exact resolve eq489429 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489429
  have eq489459 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq489436
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq489436
    | exact resolve eq489436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489436
  have eq489473 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq489459
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq489459
    | exact resolve eq489459 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489459
  have eq489487 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq489473
    | exact resolve eq489473 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489473
  have eq490843 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq476874 eq90
    | exact resolve eq90 eq476874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476874
  have eq490925 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq28 eq490843
    | exact resolve eq490843 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490843
  have eq513406 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq490925
       grind)
    | exact superpose eq490925 eq83
    | exact resolve eq83 eq490925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490925
  have eq513490 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq513406
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq513406
    | exact resolve eq513406 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513406
  have eq513499 : (σ y) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq513490
       have r₂ := eq51
       grind)
    | exact resolve eq513490 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq513490
  have eq513550 : (τ (σ y)) = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq513499 eq90
    | exact resolve eq90 eq513499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513499
  have eq513608 : y = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq513550
    | exact resolve eq513550 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513550
  have eq513615 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq513608
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq513608
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq513608 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513648 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq513608
       grind)
    | exact superpose eq513608 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq513608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513608
  have eq513663 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq513615
  have eq513671 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq513648
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq513648
       have r₂ := eq12 x y
       grind)
    | exact resolve eq513648 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513648
  have eq513681 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq513663
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq513663
    | exact resolve eq513663 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513663
  have eq513688 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq513671
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq513671
    | exact resolve eq513671 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513671
  have eq513689 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq513681
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq513681
    | exact resolve eq513681 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513681
  have eq513696 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq513688
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq513688
    | exact resolve eq513688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513688
  have eq513724 : (M.op x (M.op x y)) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq446 x
       have i₂ := eq513689
       grind)
    | exact superpose eq513689 eq446
    | exact resolve eq446 eq513689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513731 : (M.op (M.op x y) x) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61 y
       have i₂ := eq513689
       grind)
    | exact superpose eq513689 eq61
    | exact resolve eq61 eq513689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513689
  have eq515048 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq488760
       have i₂ := eq14 sF1 x sF1
       grind)
    | exact superpose eq14 eq488760
    | exact resolve eq488760 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488760
  have eq518752 : (M.op x (M.op x y)) ≠ (M.op y y) ∨ (M.op x y) = (k (M.op x y) (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq513731 eq1134
    | exact resolve eq1134 eq513731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq518755 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq513731 eq61
    | exact resolve eq61 eq513731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513731
  have eq519201 : (M.op y y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq518755
       have i₂ := eq401 y y
       grind)
    | exact superpose eq401 eq518755
    | exact resolve eq518755 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq518755
  have eq519203 : (M.op x y) = (k (M.op x y) (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq518752
       have r₂ := eq513724
       grind)
    | exact resolve eq518752 eq513724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518752
  have eq522120 : (M.op x y) = (k (M.op x y) (M.op x (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq519203
       have i₂ := eq513724
       grind)
    | exact superpose eq513724 eq519203
    | exact resolve eq519203 eq513724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513724 eq519203
  have eq522145 : (M.op x y) = (k (M.op x y) (M.op x (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq522120
  have eq530866 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq489487 eq289833
    | exact resolve eq289833 eq489487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289833
  have eq531029 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq489487 eq264835
    | exact resolve eq264835 eq489487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264835 eq489487
  have eq531030 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq531029
  have eq531049 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq530866
  have eq531085 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq531030
    | exact resolve eq531030 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531030
  have eq535478 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (k y x) ∨ y = (k y x) := by
    intro X0
    first
    | exact superpose eq476957 eq476643
    | exact resolve eq476643 eq476957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476643 eq476957
  have eq536095 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (k y x) := by
    intro X0
    first
    | (have j0 := eq535478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535478
  have eq536565 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ y = (k y x) := by
    intro X0
    first
    | exact superpose eq484 eq536095
    | exact resolve eq536095 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq536095
  have eq537628 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq536565 eq482493
    | exact resolve eq482493 eq536565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482493
  have eq537673 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (k y x) := by grind
  clear eq537628
  have eq537701 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (k y x) := by
    first
    | exact superpose eq26 eq537673
    | exact resolve eq537673 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537673
  have eq538377 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (k y x) := by
    first
    | exact superpose eq537701 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq537701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537701
  have eq538403 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (k y x) := by grind
  clear eq538377
  have eq538408 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (k y x) := by
    first
    | exact superpose eq1155 eq538403
    | exact resolve eq538403 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538403
  have eq538486 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq538408 eq536565
    | exact resolve eq536565 eq538408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536565 eq538408
  have eq538637 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by grind
  clear eq538486
  have eq594897 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq531049 eq515048
    | exact resolve eq515048 eq531049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515048 eq531049
  have eq595081 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq594897
  have eq624092 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq595081 eq30792
    | exact resolve eq30792 eq595081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30792 eq595081
  have eq624325 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq624092
  have eq627270 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq624325 eq531085
    | exact resolve eq531085 eq624325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531085 eq624325
  have eq627516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq627270
  have eq627630 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq627516
       have r₂ := eq27
       grind)
    | exact resolve eq627516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627516
  have eq627784 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq627630 eq341248
    | exact resolve eq341248 eq627630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341248 eq627630
  have eq627905 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq627784
  have eq628009 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq627905 eq90
    | exact resolve eq90 eq627905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627905
  have eq628101 : y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq628009
    | exact resolve eq628009 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628009
  have eq628107 : y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq628101
       have r₂ := eq50
       grind)
    | exact resolve eq628101 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628101
  have eq628114 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq628107
       have i₂ := eq513696
       grind)
    | exact superpose eq513696 eq628107
    | exact resolve eq628107 eq513696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513696 eq628107
  have eq639273 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq628114 eq28
    | exact resolve eq28 eq628114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq628114
  have eq640345 : x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq639273
    | exact resolve eq639273 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639273
  have eq640346 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq640345
  have eq640353 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq640346 eq20
    | exact resolve eq20 eq640346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640346
  have eq641066 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq640353
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq640353
    | exact resolve eq640353 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640353
  have eq641598 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq641066 eq538637
    | exact resolve eq538637 eq641066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538637
  have eq642001 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq641598
       have r₂ := eq50
       grind)
    | exact resolve eq641598 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641598
  have eq683895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq642001 eq405982
    | exact resolve eq405982 eq642001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405982 eq642001
  have eq684134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = y := by grind
  clear eq683895
  have eq684286 : y = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq684134
       have r₂ := eq27
       grind)
    | exact resolve eq684134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684134
  have eq684444 : x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24597
       have i₂ := eq684286
       grind)
    | exact superpose eq684286 eq24597
    | exact resolve eq24597 eq684286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24597
  have eq684465 : x = y ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq476371
       have i₂ := eq684286
       grind)
    | exact superpose eq684286 eq476371
    | exact resolve eq476371 eq684286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476371 eq684286
  have eq684486 : x = y ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq684465
  have eq684488 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq684444
  have eq684503 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq684486
       have r₂ := eq476232
       grind)
    | exact resolve eq684486 eq476232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476232 eq684486
  have eq684569 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq446 x
       have i₂ := eq684503
       grind)
    | exact superpose eq684503 eq446
    | exact resolve eq446 eq684503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq684576 : (M.op (M.op x y) x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61 y
       have i₂ := eq684503
       grind)
    | exact superpose eq684503 eq61
    | exact resolve eq61 eq684503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq684937 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq684569
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq684569
    | exact resolve eq684569 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684569
  have eq685123 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq684937 eq522145
    | exact resolve eq522145 eq684937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522145 eq684937
  have eq685370 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq685123
  have eq685587 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq684488 eq27
    | exact resolve eq27 eq684488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684488
  have eq686927 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq684576 eq46223
    | exact resolve eq46223 eq684576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46223
  have eq686943 : (M.op x y) = (M.op y x) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq684576 eq454719
    | exact resolve eq454719 eq684576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454719 eq684576
  have eq687266 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq686927
  have eq687312 : (M.op x y) = (M.op y x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq686943
       have r₂ := eq50
       grind)
    | exact resolve eq686943 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686943
  have eq688580 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq684503
       have i₂ := eq687312
       grind)
    | exact superpose eq687312 eq684503
    | exact resolve eq684503 eq687312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687312
  have eq688825 : x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq688580
  have eq688978 : y = (k y x) := by
    first
    | (have r₁ := eq688825
       have r₂ := eq50
       grind)
    | exact resolve eq688825 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq688825
  have eq689170 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq688978
       grind)
    | exact superpose eq688978 eq83
    | exact resolve eq83 eq688978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq689240 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq689170
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq689170
    | exact resolve eq689170 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689170
  have eq689782 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq689240 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq689240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689240
  have eq689797 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq689782
    | exact resolve eq689782 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689782
  have eq689814 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq689797
    | exact resolve eq689797 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689797
  have eq696851 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq685370 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq685370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685370
  have eq696877 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq696851
  have eq696889 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2555 eq696877
    | exact resolve eq696877 eq2555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696877
  have eq698186 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq684503
       have i₂ := eq687266
       grind)
    | exact superpose eq687266 eq684503
    | exact resolve eq684503 eq687266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684503 eq687266
  have eq698475 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq698186
  have eq698791 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq698475 eq1155
    | exact resolve eq1155 eq698475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq698874 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq698475 eq474099
    | exact resolve eq474099 eq698475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474099
  have eq698952 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq698874
  have eq698992 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq698952
    | exact resolve eq698952 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698952
  have eq700342 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq698791 eq473539
    | exact resolve eq473539 eq698791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473539 eq698791
  have eq700651 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq700342
  have eq704289 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq696889 eq519201
    | exact resolve eq519201 eq696889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519201 eq696889
  have eq704536 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq704289
  have eq715298 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq700651 eq698992
    | exact resolve eq698992 eq700651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698992 eq700651
  have eq715607 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq715298
  have eq716113 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq715607 eq698475
    | exact resolve eq698475 eq715607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698475 eq715607
  have eq716114 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq716113
  have eq716847 : (τ (k (σ x) (σ x))) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq716114 eq90
    | exact resolve eq90 eq716114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq716852 : (τ (k (σ x) (σ x))) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq716114 eq116
    | exact resolve eq116 eq716114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq717383 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq716114 eq641066
    | exact resolve eq641066 eq716114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641066 eq716114
  have eq717399 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq717383
  have eq717732 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq717399
       have r₂ := eq685587
       grind)
    | exact resolve eq717399 eq685587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685587 eq717399
  have eq717811 : (k x x) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49 eq716852
    | exact resolve eq716852 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716852
  have eq717814 : y = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq716847
       have i₂ := eq688978
       grind)
    | exact superpose eq688978 eq716847
    | exact resolve eq716847 eq688978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688978 eq716847
  have eq717835 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49 eq717814
    | exact resolve eq717814 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq717814
  have eq730888 : y ≠ (k x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18991 y
       have i₂ := eq717811
       grind)
    | exact superpose eq717811 eq18991
    | (have j0 := eq18991 y
       grind)
    | exact resolve eq18991 eq717811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18991 eq717811
  have eq730934 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq730888
       have r₂ := eq717835
       grind)
    | exact resolve eq730888 eq717835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717835 eq730888
  have eq731018 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq704536
       have i₂ := eq730934
       grind)
    | exact superpose eq730934 eq704536
    | exact resolve eq704536 eq730934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704536 eq730934
  have eq731277 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq731018
  have eq731900 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq731277
  have eq731915 : x = (M.op x y) := by
    first
    | (have r₁ := eq731900
       have r₂ := eq717732
       grind)
    | exact resolve eq731900 eq717732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717732 eq731900
  have eq732479 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq731915 eq20
    | exact resolve eq20 eq731915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq732483 : x ≠ x ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq731915 eq76
    | (have r₁ := eq76
       have r₂ := eq731915
       grind)
    | exact resolve eq76 eq731915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq732562 : (M.op y x) = (M.op x x) := by
    first
    | exact superpose eq731915 eq2555
    | exact resolve eq2555 eq731915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555
  have eq732694 : y = (M.op y x) ∨ y = (k x y) := by grind
  clear eq732483
  have eq732797 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq732479
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq732479
    | exact resolve eq732479 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732479
  have eq732818 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq732797 eq26
    | exact resolve eq26 eq732797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733291 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq732797 eq689814
    | exact resolve eq689814 eq732797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689814
  have eq733319 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq733291
       have r₂ := eq27
       grind)
    | exact resolve eq733291 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733291
  have eq754898 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq732694
       have i₂ := eq732562
       grind)
    | exact superpose eq732562 eq732694
    | exact resolve eq732694 eq732562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732562 eq732694
  have eq754973 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2721 x y
       have i₂ := eq754898
       grind)
    | exact superpose eq754898 eq2721
    | (have j0 := eq2721 x y
       grind)
    | exact resolve eq2721 eq754898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721 eq754898
  have eq754978 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq754973
  have eq754985 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq754978
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq754978
    | exact resolve eq754978 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754978
  have eq755015 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq754985
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq754985
    | exact resolve eq754985 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754985
  have eq755040 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq732797 eq755015
    | exact resolve eq755015 eq732797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755015
  have eq755057 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq755040
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq755040
    | exact resolve eq755040 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755040
  have eq755071 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq755057
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq755057
    | exact resolve eq755057 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755057
  have eq755085 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq755071
    | exact resolve eq755071 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq755071
  have eq755099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq732797 eq755085
    | exact resolve eq755085 eq732797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755085
  have eq755113 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq755099
       have r₂ := eq27
       grind)
    | exact resolve eq755099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755099
  have eq755210 : (M.op (M.op x y) x) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2231 x
       have i₂ := eq755113
       grind)
    | exact superpose eq755113 eq2231
    | exact resolve eq2231 eq755113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq755596 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq731915 eq755210
    | exact resolve eq755210 eq731915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755210
  have eq755712 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq755596
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq755596
    | exact resolve eq755596 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq755596
  have eq755786 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq731915 eq755712
    | exact resolve eq755712 eq731915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755712
  have eq757318 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq755113
       have i₂ := eq755786
       grind)
    | exact superpose eq755786 eq755113
    | exact resolve eq755113 eq755786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755113 eq755786
  have eq757563 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq757318
  have eq757748 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq757563 eq29
    | exact resolve eq29 eq757563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq757563
  have eq758448 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq757748
    | exact resolve eq757748 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq757748
  have eq758539 : x = y ∨ x = y := by
    first
    | exact superpose eq731915 eq758448
    | exact resolve eq758448 eq731915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731915 eq758448
  have eq758540 : x = y := by grind
  clear eq758539
  have eq758583 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq758540
       grind)
    | exact superpose eq758540 eq24
    | exact resolve eq24 eq758540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq758540
  have eq759308 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq758583
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq758583
    | exact resolve eq758583 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq758583
  have eq759430 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq732797 eq759308
    | exact resolve eq759308 eq732797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732797 eq759308
  have eq760079 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq759430 eq732818
    | exact resolve eq732818 eq759430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732818
  have eq760082 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq759430 eq733319
    | exact resolve eq733319 eq759430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733319 eq759430
  have eq760092 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq760082
       have r₂ := eq27
       grind)
    | exact resolve eq760082 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760082
  have eq761613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq760079 eq760092
    | exact resolve eq760092 eq760079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760079 eq760092
  have eq761614 : False := by grind
  exact eq761614

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_x_pxx_pxy_Equation455 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law455 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
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
  have eq56 : ∀ X0 : G, (M.op X0 (M.op y (M.op x (M.op x y)))) = X0 := by
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
  have eq57 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq14 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X1)
       have i₂ := eq60 X1 X0
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq83
    | exact resolve eq83 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq118 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq792 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq794 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq792 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq826 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq66 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq3201 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq794 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq794
    | (have j0 := eq794 (τ X0)
       grind)
    | exact resolve eq794 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq794
  have eq3211 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3201 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3201
    | (have j0 := eq3201 X0
       grind)
    | exact resolve eq3201 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201
  have eq3217 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3211 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3211
    | (have j0 := eq3211 X0
       grind)
    | exact resolve eq3211 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211
  have eq8349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq8350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq8349
    | exact resolve eq8349 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8349
  have eq8361 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq8350
       have r₂ := eq27
       grind)
    | exact resolve eq8350 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8350
  have eq8363 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq8361
    | exact resolve eq8361 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8361
  have eq8370 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8363 eq826
    | exact resolve eq826 eq8363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8363
  have eq8439 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8370 eq118
    | exact resolve eq118 eq8370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8370
  have eq8471 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq8439
    | exact resolve eq8439 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8439
  have eq8472 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3217 y
       grind)
    | (have r₁ := eq8471
       have r₂ := eq3217 y
       grind)
    | exact resolve eq8471 eq3217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3217 eq8471
  have eq8474 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq8472
       grind)
    | exact superpose eq8472 eq60
    | exact resolve eq60 eq8472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8478 : y = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq826 y
       have i₂ := eq8472
       grind)
    | exact superpose eq8472 eq826
    | exact resolve eq826 eq8472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8472
  have eq8509 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8474 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8474
    | (have j0 := eq8474 x
       grind)
    | exact resolve eq8474 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8474
  have eq8555 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8509 eq51
    | (have r₁ := eq51
       have r₂ := eq8509
       grind)
    | exact resolve eq51 eq8509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8509
  have eq8562 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8555
  have eq8585 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq793 y y
       have i₂ := eq8478
       grind)
    | exact superpose eq8478 eq793
    | (have j0 := eq793 y y
       grind)
    | exact resolve eq793 eq8478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8478
  have eq8588 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8585
  have eq8589 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8588
  have eq8594 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8589
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8589
    | exact resolve eq8589 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8589
  have eq8844 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8594 eq60
    | exact resolve eq60 eq8594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8594
  have eq9114 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8562 eq55
    | exact resolve eq55 eq8562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8562
  have eq9133 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq9114
    | exact resolve eq9114 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9114
  have eq9138 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9133
       have r₂ := eq50
       grind)
    | exact resolve eq9133 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9133
  have eq9346 : x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq9138
       grind)
    | exact superpose eq9138 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq9138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9138
  have eq9347 : x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9346
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9346
    | exact resolve eq9346 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9346
  have eq9348 : x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq9347
  have eq9359 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9348
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9348
    | exact resolve eq9348 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9348
  have eq9394 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8844
    | (have j0 := eq8844 (σ x)
       grind)
    | exact resolve eq8844 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8844
  have eq9697 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9394 eq51
    | (have r₁ := eq51
       have r₂ := eq9394
       grind)
    | exact resolve eq51 eq9394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq9394
  have eq9705 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9697
  have eq10889 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq9359
       grind)
    | exact superpose eq9359 eq60
    | exact resolve eq60 eq9359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9359
  have eq11863 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9705 eq55
    | exact resolve eq55 eq9705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq9705
  have eq11886 : x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq11863
    | exact resolve eq11863 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11863
  have eq11892 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11886
       have r₂ := eq50
       grind)
    | exact resolve eq11886 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq11886
  have eq11895 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11892
       grind)
    | exact superpose eq11892 eq44
    | exact resolve eq44 eq11892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq11892
  have eq11916 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11895
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11895
    | exact resolve eq11895 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11895
  have eq12062 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11916 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq11916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11916
  have eq12063 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12062
    | exact resolve eq12062 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12062
  have eq12064 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12063
  have eq12077 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12064
    | exact resolve eq12064 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12064
  have eq12117 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10889 x
       grind)
    | exact superpose eq10889 eq18
    | (have j1 := eq10889 x
       grind)
    | exact resolve eq18 eq10889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10889
  have eq12118 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12117
  have eq12146 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12118 eq20
    | exact resolve eq20 eq12118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12118
  have eq12262 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12146
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12146
    | exact resolve eq12146 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12146
  have eq19129 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq12077 eq60
    | exact resolve eq60 eq12077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12077
  have eq19368 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19129 eq26
    | (have j1 := eq19129 (σ x)
       grind)
    | exact resolve eq26 eq19129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19129
  have eq19369 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19368
  have eq19412 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19369 eq27
    | exact resolve eq27 eq19369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19369
  have eq19557 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12262 eq19412
    | (have r₁ := eq19412
       have r₂ := eq12262
       grind)
    | exact resolve eq19412 eq12262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12262 eq19412
  have eq19558 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19557
  have eq19684 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19558 eq57
    | exact resolve eq57 eq19558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq19558
  have eq19695 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19684 X0
       have i₂ := eq60 sF2 sF3
       grind)
    | exact superpose eq60 eq19684
    | exact resolve eq19684 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19684
  have eq19706 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19695 eq826
    | exact resolve eq826 eq19695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19695
  have eq19920 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19706 eq118
    | exact resolve eq118 eq19706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq19706
  have eq19976 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq19920
    | exact resolve eq19920 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19920
  have eq20325 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq19976
       grind)
    | exact superpose eq19976 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq19976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19976
  have eq20337 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq20325
  have eq20630 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq20337
       grind)
    | exact superpose eq20337 eq60
    | exact resolve eq60 eq20337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20337
  have eq21004 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20630 x
       grind)
    | exact superpose eq20630 eq18
    | (have j1 := eq20630 x
       grind)
    | exact resolve eq18 eq20630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20630
  have eq21007 : x = (M.op x y) := by grind
  clear eq21004
  have eq21048 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21007 eq20
    | exact resolve eq20 eq21007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq21051 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
    intro X0
    first
    | exact superpose eq21007 eq56
    | exact resolve eq56 eq21007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq21007
  have eq21158 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq21051 X0
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq21051
    | exact resolve eq21051 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21051
  have eq21160 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21048
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21048
    | exact resolve eq21048 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21048
  have eq21164 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21160 eq26
    | exact resolve eq26 eq21160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq21160
  have eq21309 : y = (k y y) := by
    first
    | (have i₁ := eq826 y
       have i₂ := eq21158 y
       grind)
    | exact superpose eq21158 eq826
    | exact resolve eq826 eq21158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826 eq21158
  have eq21518 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq793 y y
       have i₂ := eq21309
       grind)
    | exact superpose eq21309 eq793
    | (have j0 := eq793 y y
       grind)
    | exact resolve eq793 eq21309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq21309
  have eq21519 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq21518
  have eq21520 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq21519
  have eq21530 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21520
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21520
    | exact resolve eq21520 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq21520
  have eq21638 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq21530 eq60
    | exact resolve eq60 eq21530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq21530
  have eq21834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21638 eq21164
    | exact resolve eq21164 eq21638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21164 eq21638
  have eq21838 : False := by grind
  exact eq21838

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxy_x_pyx_Equation455 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law455 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq14 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X1) X0
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq77 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) ≠ (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X0 (M.op X1 (M.op X1 X0))) X2) ∨ (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
       have i₂ := eq14 (M.op X0 (M.op X1 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       have r₂ := eq14 (M.op X1 (M.op X2 (M.op X2 X1))) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X0 (M.op X1 (M.op X1 X0))) X2) ∨ (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq77 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq97 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq178 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq199 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq354 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq742 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq98 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq744 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq742 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq851 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) ≠ (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
       have i₂ := eq80 X0 X1 X2
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
       have j1 := eq80 X0 X1 X2
       grind)
    | (have r₁ := eq13 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
       have r₂ := eq80 X0 X1 X2
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq862 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq851 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq866 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = X2 ∨ (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq862 X0 X1 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq862
    | (have j0 := eq862 X0 X1 X2
       grind)
    | exact resolve eq862 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq867 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq866 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq897 : ∀ X0 : G, (k X0 (M.op y (M.op x (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq867 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq867
    | (have j0 := eq867 y x X0
       grind)
    | exact resolve eq867 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 : G, (k X0 (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq867
    | (have j0 := eq867 (σ y) (σ x) X0
       grind)
    | exact resolve eq867 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq867 X0 X0 X1
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq867
    | exact resolve eq867 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq940 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq354 X0 (M.op X1 X1)
       have i₂ := eq900 X1 (σ X0)
       grind)
    | exact superpose eq900 eq354
    | exact resolve eq354 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq940 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq940
    | exact resolve eq940 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq1146 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq898 eq354
    | exact resolve eq354 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq898
  have eq1154 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1146 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1146
    | exact resolve eq1146 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq4448 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq744 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq744
    | (have j0 := eq744 (τ X0)
       grind)
    | exact resolve eq744 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq4487 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4448 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4448
    | (have j0 := eq4448 X0
       grind)
    | exact resolve eq4448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4448
  have eq4517 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4487 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4487
    | (have j0 := eq4487 X0
       grind)
    | exact resolve eq4487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4487
  have eq5561 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq178
    | (have j0 := eq178 x
       grind)
    | exact resolve eq178 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq5573 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5561
  have eq5577 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5573
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq5573
    | exact resolve eq5573 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq5573
  have eq5594 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5577
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5577 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5577
  have eq5600 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5594 eq49
    | exact resolve eq49 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq5594
  have eq5817 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq199 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq199
    | (have j0 := eq199 y
       grind)
    | exact resolve eq199 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq5828 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5817
  have eq5831 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5828
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq5828
    | exact resolve eq5828 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq5828
  have eq5854 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5831
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5831 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5831
  have eq5888 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5854 eq97
    | exact resolve eq97 eq5854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq5854
  have eq5894 : ∀ X0 : G, (k X0 (k y y)) = X0 := by
    intro X0
    first
    | exact superpose eq5888 eq945
    | exact resolve eq945 eq5888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq5888
  have eq5968 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (k y y)) := by
    intro X0
    first
    | (have i₁ := eq5894 (M.op X0 X0)
       have i₂ := eq72 (k y y) X0
       grind)
    | exact superpose eq72 eq5894
    | exact resolve eq5894 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5894
  have eq7570 : ∀ X0 X1 : G, (M.op X1 (M.op (k y y) (M.op (M.op X0 X0) (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (k y y) (M.op X0 X0)
       have i₂ := eq5968 X0
       grind)
    | exact superpose eq5968 eq14
    | exact resolve eq14 eq5968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968
  have eq7588 : ∀ X1 : G, (M.op X1 (k y y)) = X1 := by
    intro X1
    first
    | (have i₁ := eq7570 x X1
       have i₂ := eq54 (M.op x x) (k y y)
       grind)
    | exact superpose eq54 eq7570
    | exact resolve eq7570 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7570
  have eq20636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq20643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq20636
    | exact resolve eq20636 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20636
  have eq20654 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq20643
       have r₂ := eq27
       grind)
    | exact resolve eq20643 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20643
  have eq20656 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq20654
    | exact resolve eq20654 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20654
  have eq20658 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20656 eq5600
    | exact resolve eq5600 eq20656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5600 eq20656
  have eq20699 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq20658
    | exact resolve eq20658 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20658
  have eq20702 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq4517 x
       grind)
    | (have r₁ := eq20699
       have r₂ := eq4517 x
       grind)
    | exact resolve eq20699 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4517 eq20699
  have eq20705 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq72 X0 x
       have i₂ := eq20702
       grind)
    | exact superpose eq20702 eq72
    | exact resolve eq72 eq20702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20706 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq900 x X0
       have i₂ := eq20702
       grind)
    | exact superpose eq20702 eq900
    | exact resolve eq900 eq20702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq20702
  have eq21018 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq744 x
       have i₂ := eq20706 x
       grind)
    | exact superpose eq20706 eq744
    | (have j0 := eq744 x
       grind)
    | exact resolve eq744 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20706
  have eq21045 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21018
  have eq21064 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21045
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21045
    | exact resolve eq21045 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21045
  have eq21882 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21064 eq72
    | exact resolve eq72 eq21064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq21064
  have eq23094 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20705 y
       grind)
    | exact superpose eq20705 eq44
    | exact resolve eq44 eq20705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq20705
  have eq23125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23094
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23094
    | exact resolve eq23094 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23094
  have eq23156 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23125
    | exact resolve eq23125 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23125
  have eq25142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21882 eq23156
    | exact resolve eq23156 eq21882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21882 eq23156
  have eq25143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25142
  have eq25163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq25143
    | exact resolve eq25143 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25143
  have eq25181 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25163
       have r₂ := eq27
       grind)
    | exact resolve eq25163 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25163
  have eq25193 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (M.op (σ x) (σ x))))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25181 eq1154
    | exact resolve eq1154 eq25181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq25181
  have eq25203 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25193 X0
       have i₂ := eq54 sF2 sF3
       grind)
    | exact superpose eq54 eq25193
    | exact resolve eq25193 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25193
  have eq25209 : ∀ X0 : G, (k X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq25203
    | exact resolve eq25203 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25203
  have eq25596 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7588 X0
       have i₂ := eq25209 y
       grind)
    | exact superpose eq25209 eq7588
    | exact resolve eq7588 eq25209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7588 eq25209
  have eq26073 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25596 x
       grind)
    | exact superpose eq25596 eq18
    | (have j1 := eq25596 x
       grind)
    | exact resolve eq18 eq25596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25596
  have eq26074 : x = (M.op x y) := by grind
  clear eq26073
  have eq26092 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq26074 eq20
    | exact resolve eq20 eq26074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq26149 : ∀ X0 : G, (k X0 (M.op y (M.op x x))) = X0 := by
    intro X0
    first
    | exact superpose eq26074 eq897
    | exact resolve eq897 eq26074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq26074
  have eq26175 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26149 X0
       have i₂ := eq54 x y
       grind)
    | exact superpose eq54 eq26149
    | exact resolve eq26149 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26149
  have eq26229 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq26092
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26092
    | exact resolve eq26092 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26092
  have eq26581 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26229 eq26
    | exact resolve eq26 eq26229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq26229
  have eq26830 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq744 y
       have i₂ := eq26175 y
       grind)
    | exact superpose eq26175 eq744
    | (have j0 := eq744 y
       grind)
    | exact resolve eq744 eq26175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq26175
  have eq26863 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq26830
  have eq26890 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26863
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26863
    | exact resolve eq26863 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq26863
  have eq27526 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq26890 eq54
    | exact resolve eq54 eq26890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq26890
  have eq28454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27526 eq26581
    | exact resolve eq26581 eq27526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26581 eq27526
  have eq28461 : False := by grind
  exact eq28461

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyy_y_pyx_pxy_pyx_Equation4554 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4554 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
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
  clear eq24
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X2 X0) X3) ∨ (k (M.op X2 X0) X3) = (M.op X3 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X2 X0) X3
       have i₂ := eq14 (M.op X2 X0) X2 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X2 X0) X3
       grind)
    | (have r₁ := eq13 (M.op X3 X3) X3
       have r₂ := eq14 (M.op X3 X3) X3 X3 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq49
    | exact resolve eq49 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq80 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq79
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq79
    | exact resolve eq79 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq77
    | exact resolve eq77 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq86 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq109 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq109
    | (have j1 := eq86 x x
       grind)
    | exact resolve eq109 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq124
    | exact resolve eq124 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq337 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq58 x x
       have i₂ := eq14 x x x X0
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2 (M.op x x)
       have i₂ := eq58 X2 x
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq75 (τ X0)
       grind)
    | exact superpose eq75 eq34
    | exact resolve eq34 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq425 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq414 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq414
    | exact resolve eq414 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq427 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq425 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq425
    | exact resolve eq425 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq2608 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 x X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq3113 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq82 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq82
    | exact resolve eq82 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq82
  have eq3151 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq3113
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq3113
    | exact resolve eq3113 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113
  have eq3154 : (σ (M.op (M.op x y) x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq3151
       have i₂ := eq58 (M.op x x) x
       grind)
    | exact superpose eq58 eq3151
    | exact resolve eq3151 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151
  have eq3156 : (σ (M.op (M.op x y) x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq3154
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq3154
    | exact resolve eq3154 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq3154
  have eq3157 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq59 eq3156
    | exact resolve eq3156 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq4148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq125 eq86
    | (have j0 := eq86 x (σ x)
       grind)
    | exact resolve eq86 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq125
  have eq4149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq4148
    | exact resolve eq4148 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148
  have eq4152 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq4149
       have r₂ := eq27
       grind)
    | exact resolve eq4149 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149
  have eq4155 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4152 eq80
    | exact resolve eq80 eq4152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq4152
  have eq4191 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq4155
    | exact resolve eq4155 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4155
  have eq4192 : x = (M.op x x) := by grind
  clear eq4191
  have eq4197 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | (have i₁ := eq337 x
       have i₂ := eq4192
       grind)
    | exact superpose eq4192 eq337
    | exact resolve eq337 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq4236 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq4197
       have i₂ := eq4192
       grind)
    | exact superpose eq4192 eq4197
    | exact resolve eq4197 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192 eq4197
  have eq4392 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq4236 eq3157
    | exact resolve eq3157 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3157
  have eq4393 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq4236 eq58
    | exact resolve eq58 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq4236
  have eq4417 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq4392
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4392
    | exact resolve eq4392 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4392
  have eq4740 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq343 X0 X1 X2
       have i₂ := eq4393 sF0
       grind)
    | exact superpose eq4393 eq343
    | exact resolve eq343 eq4393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq4393
  have eq4850 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq59 x x
       have i₂ := eq4740 x x sF2
       grind)
    | exact superpose eq4740 eq59
    | exact resolve eq59 eq4740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq4926 : (σ x) = (M.op x (σ x)) := by
    first
    | exact superpose eq4417 eq4850
    | exact resolve eq4850 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4417 eq4850
  have eq5026 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq4926 eq4740
    | exact resolve eq4740 eq4926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4926
  have eq5194 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ x) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq5026 eq362
    | exact resolve eq362 eq5026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq5026
  have eq5195 : ∀ X2 : G, (M.op x X2) = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq5194 x x X2
       have i₂ := eq4740 x x X2
       grind)
    | exact superpose eq4740 eq5194
    | exact resolve eq5194 eq4740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5194
  have eq5196 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq26 eq5195
    | (have j0 := eq5195 (σ y)
       grind)
    | exact resolve eq5195 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5195
  have eq6923 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2608 X0
       have i₂ := eq4740 X0 X0 X0
       grind)
    | exact superpose eq4740 eq2608
    | exact resolve eq2608 eq4740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2608 eq4740
  have eq6963 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq6923 (τ X0)
       grind)
    | exact superpose eq6923 eq38
    | exact resolve eq38 eq6923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq6964 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6963 X0
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq6963
    | exact resolve eq6963 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq6963
  have eq7000 : ∀ X0 : G, (M.op x X0) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6964 X0
       have i₂ := eq6923 X0
       grind)
    | exact superpose eq6923 eq6964
    | exact resolve eq6964 eq6923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6923 eq6964
  have eq7685 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq29 eq7000
    | exact resolve eq7000 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7000
  have eq7702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5196 eq7685
    | exact resolve eq7685 eq5196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5196 eq7685
  have eq7712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7702
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7702
    | exact resolve eq7702 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7702
  have eq7721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq7712
    | exact resolve eq7712 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7712
  have eq7725 : False := by grind
  exact eq7725

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pyx_pxy_pyx_Equation4554 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4554 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq177 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X4) X0) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 x x X0 X4
       have i₂ := eq16 x x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 X3 X4 (M.op x X0)
       have i₂ := eq16 X4 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (M.op x y) = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq200 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq177 X2 x
       have i₂ := eq177 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq200 eq177
    | exact resolve eq177 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X1 (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X1
    first
    | exact superpose eq184 eq178
    | exact resolve eq178 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq884 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X2 X0) X3) ∨ (M.op (M.op X2 X0) X3) = (k X3 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X2 X0)
       have i₂ := eq16 (M.op X2 X0) X2 X0 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X3 (M.op X2 X0)
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq16 (M.op X1 X1) X1 X1 X1
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (k x x)) := by
    intro X0
    first
    | (have i₁ := eq183 X0 x
       have i₂ := eq895 x
       grind)
    | exact superpose eq895 eq183
    | exact resolve eq183 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq200 X0 sF0
       have i₂ := eq895 sF0
       grind)
    | exact superpose eq895 eq200
    | exact resolve eq200 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq1064 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq184 X0 sF2
       have i₂ := eq895 sF2
       grind)
    | exact superpose eq895 eq184
    | exact resolve eq184 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1067 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq240 X0 sF4
       have i₂ := eq895 sF4
       grind)
    | exact superpose eq895 eq240
    | exact resolve eq240 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq1101 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | exact superpose eq1060 eq177
    | exact resolve eq177 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1108 : ∀ X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X1 (M.op x y)) y) := by
    intro X1
    first
    | exact superpose eq1060 eq235
    | exact resolve eq235 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq1119 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1060 eq16
    | exact resolve eq16 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1125 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1060 eq1119
    | exact resolve eq1119 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1130 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq1060 eq1108
    | exact resolve eq1108 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060 eq1108
  have eq1158 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1067 eq304
    | exact resolve eq304 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq1165 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1067 eq16
    | exact resolve eq16 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1170 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1067 eq1165
    | exact resolve eq1165 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067 eq1165
  have eq2631 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq195
       grind)
    | exact superpose eq195 eq40
    | exact resolve eq40 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq2632 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2631
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2631
    | exact resolve eq2631 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq2634 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq2632
    | exact resolve eq2632 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632
  have eq2725 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2634 eq196
    | exact resolve eq196 eq2634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq2634
  have eq2732 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq2725
       have r₂ := eq27
       grind)
    | exact resolve eq2725 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2739 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2732 eq184
    | exact resolve eq184 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq2781 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq2739 eq2739
    | exact resolve eq2739 eq2739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739
  have eq2803 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq2781 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781
  have eq2882 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2803 eq895
    | exact resolve eq895 eq2803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2902 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2803 eq2732
    | exact resolve eq2732 eq2803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732 eq2803
  have eq2913 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902
  have eq2940 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2913 eq2882
    | exact resolve eq2882 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882 eq2913
  have eq3049 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2940 eq142
    | exact resolve eq142 eq2940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq2940
  have eq3052 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq3049
    | exact resolve eq3049 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3049
  have eq4133 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1057 X0
       have i₂ := eq3052
       grind)
    | exact superpose eq3052 eq1057
    | exact resolve eq1057 eq3052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq5302 : (k x x) = (M.op (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq895 x
       have i₂ := eq4133 x
       grind)
    | exact superpose eq4133 eq895
    | exact resolve eq895 eq4133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5327 : x ≠ (M.op (M.op x y) x) ∨ x = (M.op y x) := by grind
  clear eq4133
  have eq5335 : x = (M.op (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3052 eq5302
    | exact resolve eq5302 eq3052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052 eq5302
  have eq5346 : x = (M.op y x) := by
    first
    | (have r₁ := eq5335
       have r₂ := eq5327
       grind)
    | exact resolve eq5335 eq5327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5327 eq5335
  have eq5353 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1101 x
       have i₂ := eq5346
       grind)
    | exact superpose eq5346 eq1101
    | exact resolve eq1101 eq5346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq5355 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq183 X0 y
       have i₂ := eq5346
       grind)
    | exact superpose eq5346 eq183
    | exact resolve eq183 eq5346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq5362 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 y x X0 X1 X2
       have i₂ := eq5346
       grind)
    | exact superpose eq5346 eq181
    | exact resolve eq181 eq5346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq5368 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5362 X0 X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5362
    | (have j0 := eq5362 X0 X1 X2
       grind)
    | exact resolve eq5362 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5362
  have eq5376 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5353
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5353
    | exact resolve eq5353 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5353
  have eq5389 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5376 eq1125
    | exact resolve eq1125 eq5376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq5390 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq5376 eq1130
    | exact resolve eq1130 eq5376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq5376
  have eq5446 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq5389 eq179
    | exact resolve eq179 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq5389
  have eq5587 : (k x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq895 x
       have i₂ := eq5355 x
       grind)
    | exact superpose eq5355 eq895
    | exact resolve eq895 eq5355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5606 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq5346
       have i₂ := eq5355 y
       grind)
    | exact superpose eq5355 eq5346
    | exact resolve eq5346 eq5355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5346 eq5355
  have eq5620 : x = (k x x) := by
    first
    | exact superpose eq5606 eq5587
    | exact resolve eq5587 eq5606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5587 eq5606
  have eq5679 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq5620
       grind)
    | exact superpose eq5620 eq40
    | exact resolve eq40 eq5620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5620
  have eq5682 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq5679
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5679
    | exact resolve eq5679 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5679
  have eq5778 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq5682 eq1064
    | exact resolve eq1064 eq5682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq7301 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X0 (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq5778 eq5778
    | exact resolve eq5778 eq5778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5778
  have eq7514 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq7301 eq895
    | exact resolve eq895 eq7301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7301
  have eq7579 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq5682 eq7514
    | exact resolve eq7514 eq5682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5682 eq7514
  have eq7705 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7579 eq1158
    | exact resolve eq1158 eq7579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq7579
  have eq7711 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq7705
    | exact resolve eq7705 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq7705
  have eq7751 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq7711 eq1170
    | exact resolve eq1170 eq7711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170 eq7711
  have eq7810 : ∀ X1 X2 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op X2 (σ y))) := by
    intro X1 X2
    first
    | exact superpose eq7751 eq246
    | exact resolve eq246 eq7751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq7751
  have eq7875 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq7810 x x
       have i₂ := eq5368 x x sF3
       grind)
    | exact superpose eq5368 eq7810
    | exact resolve eq7810 eq5368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5368 eq7810
  have eq12168 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq5446 X0 X0
       have i₂ := eq895 X0
       grind)
    | exact superpose eq895 eq5446
    | exact resolve eq5446 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5446
  have eq21087 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq884 X0 x X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq21088 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21087 X0
       have i₂ := eq895 X0
       grind)
    | exact superpose eq895 eq21087
    | exact resolve eq21087 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq21087
  have eq21485 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21088 X0
       have i₂ := eq12168 X0
       grind)
    | exact superpose eq12168 eq21088
    | exact resolve eq21088 eq12168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12168 eq21088
  have eq23439 : (σ (M.op (M.op x y) y)) = (k (σ y) (σ (k y y))) := by
    first
    | (have i₁ := eq37 (k y y)
       have i₂ := eq21485 y
       grind)
    | exact superpose eq21485 eq37
    | exact resolve eq37 eq21485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq23449 : (σ (M.op (M.op x y) y)) = (k (σ y) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq23439
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq23439
    | exact resolve eq23439 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq23439
  have eq23465 : (k (σ y) (k (σ y) (σ y))) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq23449
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23449
    | exact resolve eq23449 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq23449
  have eq23477 : (σ (M.op x y)) = (k (σ y) (k (σ y) (σ y))) := by
    first
    | exact superpose eq5390 eq23465
    | exact resolve eq23465 eq5390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5390 eq23465
  have eq23486 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq23477
       have i₂ := eq21485 sF3
       grind)
    | exact superpose eq21485 eq23477
    | exact resolve eq23477 eq21485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21485 eq23477
  have eq23493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7875 eq23486
    | exact resolve eq23486 eq7875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7875 eq23486
  have eq23496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23493
    | exact resolve eq23493 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq23493
  have eq23498 : False := by grind
  exact eq23498

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
       have r₂ := eq14 X1 X1
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
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq83 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq285 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq292 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq285 X0 X1
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq285 X0 X1
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq285 X0 X0
       have r₂ := eq76 X0 X0
       grind)
    | exact resolve eq285 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq285
  have eq391 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq292 (σ X1) (σ X0)
       grind)
    | exact superpose eq292 eq15
    | exact resolve eq15 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq292 X1 X0
       grind)
    | exact superpose eq292 eq391
    | exact resolve eq391 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq391
  have eq398 : False := by grind
  exact eq398

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq52 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq29 (σ X0)
       grind)
    | exact superpose eq29 eq15
    | exact resolve eq15 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq52
    | exact resolve eq52 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52
  have eq76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq47 (σ X1) (σ X0)
       grind)
    | exact superpose eq47 eq15
    | (have j1 := eq47 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq76
    | (have j0 := eq76 X0 X1
       have j1 := eq47 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq76 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq76
  have eq8348 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq699 x y
       grind)
    | exact superpose eq699 eq16
    | (have j1 := eq699 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq699 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq699 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq699 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq8426 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq8348
  have eq8573 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8426
       grind)
    | exact superpose eq8426 eq10
    | exact resolve eq10 eq8426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8426
  have eq8626 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8573
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8573
    | exact resolve eq8573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8573
  have eq8627 : x = y := by grind
  clear eq8626
  have eq11851 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8627
       grind)
    | exact superpose eq8627 eq16
    | exact resolve eq16 eq8627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8627
  have eq11852 : False := by grind
  exact eq11852
