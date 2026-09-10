import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pxy_Equation3888 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3888 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X0 X1)) X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq70 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 (σ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq39
    | (have j0 := eq39 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq39 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq124 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq103
    | (have j0 := eq103 X0 X1
       grind)
    | exact resolve eq103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq313 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq327 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq313 X0 X1
       have j1 := eq118 X0 X1
       grind)
    | (have r₁ := eq313 X0 X1
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq313 X0 X0
       have r₂ := eq118 X0 X0
       grind)
    | (have r₁ := eq313 (M.op X0 X1) (M.op X1 X1)
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq313 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq313
  have eq364 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq41
    | (have j0 := eq41 X0 X1
       have j1 := eq40 X0 X1
       grind)
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq695 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq327 X0 X1
       grind)
    | exact superpose eq327 eq41
    | (have j0 := eq41 X0 X1
       have j1 := eq327 (σ (M.op X0 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq41 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq748 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op (M.op X0 (M.op X0 (σ X1))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5079 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X1 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq327 X0 X1
       grind)
    | exact superpose eq327 eq124
    | (have j0 := eq124 (M.op X1 X1) (M.op X0 X1)
       have j1 := eq327 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq124 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq327
  have eq36771 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq364 x y
       grind)
    | exact superpose eq364 eq16
    | (have j1 := eq364 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq364 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq364 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq364 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq37292 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq36771
  have eq46768 : (M.op y y) = (τ (M.op (M.op (σ x) (σ (M.op x x))) (σ x))) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq748 (σ x) y
       have i₂ := eq37292
       grind)
    | exact superpose eq37292 eq748
    | exact resolve eq748 eq37292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748 eq37292
  have eq46957 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46768
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq46768
    | exact resolve eq46768 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq46768
  have eq46974 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46957
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq46957
    | exact resolve eq46957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46957
  have eq46975 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq46974
  have eq65019 : ∀ X0 : G, (σ (M.op x x)) = (M.op (M.op X0 (M.op X0 (σ y))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq70 y X0
       have i₂ := eq46975
       grind)
    | exact superpose eq46975 eq70
    | exact resolve eq70 eq46975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46975
  have eq112098 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq70 y x
       have i₂ := eq65019 x
       grind)
    | exact superpose eq65019 eq70
    | exact resolve eq70 eq65019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq65019
  have eq192037 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq5079 x y
       grind)
    | exact superpose eq5079 eq16
    | (have j1 := eq5079 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq5079 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq5079 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq5079 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq5079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5079
  have eq192787 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq192037
  have eq200662 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq695 x y
       grind)
    | exact superpose eq695 eq16
    | (have j1 := eq695 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq695 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq695 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq695 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq200978 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq200662
  have eq201635 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq112098
       have i₂ := eq192787
       grind)
    | exact superpose eq192787 eq112098
    | exact resolve eq112098 eq192787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112098 eq192787
  have eq201871 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq201635
  have eq346553 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq200978
       grind)
    | exact superpose eq200978 eq16
    | exact resolve eq16 eq200978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200978
  have eq347070 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq346553
       have r₂ := eq201871
       grind)
    | exact resolve eq346553 eq201871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201871 eq346553
  have eq373628 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq347070
       grind)
    | exact superpose eq347070 eq10
    | exact resolve eq10 eq347070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347070
  have eq373975 : x = y ∨ x = y := by
    first
    | (have i₁ := eq373628
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq373628
    | exact resolve eq373628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373628
  have eq373976 : x = y := by grind
  clear eq373975
  have eq406122 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq373976
       grind)
    | exact superpose eq373976 eq16
    | exact resolve eq16 eq373976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373976
  have eq406123 : False := by grind
  exact eq406123

/-- `Equation4403`: `x ◇ (x ◇ y) = (x ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pyx_x_pyx_Equation4403 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4403 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4403.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X2) := by
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
  have eq50 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X0 (M.op X0 x) X3
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X2) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X0 x X3
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X2 (M.op X0 X3)
       have i₂ := eq14 X0 X3 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X2) X3 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq94 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
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
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq95
    | (have j0 := eq95 (σ X0) (σ X1)
       grind)
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq95 y x
       grind)
    | exact superpose eq95 eq73
    | (have j1 := eq95 y x
       grind)
    | exact resolve eq73 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq110 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq95 y sF0
       grind)
    | exact superpose eq95 eq75
    | (have j1 := eq95 y (M.op x y)
       grind)
    | exact resolve eq75 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq127 : (σ (k (M.op x y) (k y y))) = (k (σ (M.op x y)) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq37 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq37
    | exact resolve eq37 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq130 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq206 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq55 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 (σ y)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq345 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq375 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq52 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x X0 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) X0 (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq215 eq378
    | exact resolve eq378 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq395 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq206 eq375
    | exact resolve eq375 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq514 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X2) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 X0 (M.op X0 X3) X2
       have i₂ := eq57 X0 X3 X1
       grind)
    | (have i₁ := eq50 X0 (M.op X0 X3) X2
       have i₂ := eq57 X0 X1 X3
       grind)
    | exact superpose eq57 eq50
    | exact resolve eq50 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq715 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X3)) = (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op X0 X1) X3 X1
       have i₂ := eq52 (M.op X0 (M.op X0 X1)) (M.op X0 X1) X2
       grind)
    | (have i₁ := eq53 X0 (M.op X0 X1) X3 X1
       have i₂ := eq52 (M.op X0 (M.op X0 X1)) X2 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X3)) = (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op X0 X1) X3 X1
       have i₂ := eq14 (M.op X0 (M.op X0 X1)) X2 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x X0) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x
       have i₂ := eq53 x X0 x X1
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (M.op x X1)) := by
    intro X1
    first
    | (have i₁ := eq730 x X1
       have i₂ := eq395 x
       grind)
    | exact superpose eq395 eq730
    | exact resolve eq730 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq773 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op x X1)) := by
    intro X1
    first
    | exact superpose eq206 eq755
    | exact resolve eq755 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq827 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq267 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq267
    | (have j0 := eq267 X0 y
       grind)
    | exact resolve eq267 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq961 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X3) (M.op (M.op X0 X1) (M.op X0 (M.op X0 X2)))) = (M.op (M.op (M.op X0 X1) X3) (M.op (M.op (M.op X0 X1) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 (M.op (M.op X0 X1) X3) X3 X4
       have i₂ := eq51 X0 X2 X1 X3
       grind)
    | exact superpose eq51 eq57
    | exact resolve eq57 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X2) ∨ (k (M.op X0 (M.op X0 X1)) X3) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 (M.op X0 X1)) X3
       have i₂ := eq51 X0 X1 (M.op X0 X1) X2
       grind)
    | exact superpose eq51 eq13
    | (have j0 := eq13 (M.op X0 (M.op X0 X1)) X3
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1115 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X1) X1)) = (M.op (M.op X0 (M.op X0 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X0 X3 X2 X2
       have i₂ := eq52 X0 X2 X1
       grind)
    | (have i₁ := eq54 X0 X3 X2 X2
       have i₂ := eq52 X0 X1 X2
       grind)
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X2) (M.op (M.op X0 (M.op X0 X1)) X2)) = (M.op (M.op X0 (M.op X0 X4)) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq54 X0 X4 X2 (M.op (M.op X0 X2) x)
       have i₂ := eq54 X0 X1 X2 x
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1156 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op x X0) X1)) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 x x X0 X1
       have i₂ := eq55 x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1157 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1175 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) = (M.op (M.op (M.op (M.op X0 (M.op X0 X1)) X2) (M.op (M.op X0 X2) X4)) (M.op (M.op X0 X2) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X0 X2) (M.op (M.op X0 X2) X4) X3 X5
       have i₂ := eq54 X0 X1 X2 X4
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq1196 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq215 eq1157
    | exact resolve eq1157 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1197 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op x X0) X1)) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq206 eq1156
    | exact resolve eq1156 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq121 eq95
    | (have j0 := eq95 (σ y) (σ x)
       grind)
    | exact resolve eq95 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1214
    | exact resolve eq1214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1218 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1215
       have r₂ := eq27
       grind)
    | exact resolve eq1215 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1221 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1218 eq14
    | exact resolve eq14 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1279 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X1) X2) X2) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (σ X1) (σ X0) X2
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq52
    | (have j1 := eq99 X0 X1
       grind)
    | exact resolve eq52 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq99 X0 X0
       grind)
    | exact superpose eq99 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq99 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq99 X1 X1
       grind)
    | exact resolve eq13 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1289 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq99 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1290 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1288 X0 X1
       have j1 := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq1288 X0 X1
       have r₂ := eq13 (σ X0) X1
       grind)
    | exact resolve eq1288 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1306 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1218 eq1221
    | exact resolve eq1221 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1340 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1306
  have eq1342 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1340 eq1218
    | exact resolve eq1218 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1357 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1342
  have eq1377 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1357 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq1357
       grind)
    | exact resolve eq13 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1378 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1426 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1378 eq49
    | exact resolve eq49 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1427 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1378 eq61
    | exact resolve eq61 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1555 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1357 eq1426
    | exact resolve eq1426 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357 eq1426
  have eq1568 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) := by grind
  clear eq1555
  have eq1570 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq1568
    | exact resolve eq1568 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568
  have eq1573 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq95 x x
       have i₂ := eq1570
       grind)
    | exact superpose eq1570 eq95
    | (have j0 := eq95 x x
       grind)
    | exact resolve eq95 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq1574 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq1573
  have eq1581 : ∀ X0 : G, (M.op x x) = (M.op y (M.op y X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq1574
       grind)
    | exact superpose eq1574 eq14
    | exact resolve eq14 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1610 : (τ (σ x)) = (k x y) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1218 eq1427
    | exact resolve eq1427 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218 eq1427
  have eq1623 : (τ (σ x)) = (k x y) ∨ x = (M.op y x) := by grind
  clear eq1610
  have eq1626 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq1623
    | exact resolve eq1623 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq339479 : (M.op x x) = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1581 x
       have i₂ := eq1574
       grind)
    | exact superpose eq1574 eq1581
    | exact resolve eq1581 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq340034 : (M.op x x) = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq339479
  have eq340136 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1574
       have i₂ := eq340034
       grind)
    | exact superpose eq340034 eq1574
    | exact resolve eq1574 eq340034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574 eq340034
  have eq340466 : x = (M.op x x) := by grind
  clear eq340136
  have eq344064 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq395 x
       have i₂ := eq340466
       grind)
    | exact superpose eq340466 eq395
    | exact resolve eq395 eq340466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq344066 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq340466
       grind)
    | exact superpose eq340466 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq340466
       grind)
    | exact resolve eq13 eq340466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344335 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq344066 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344066
  have eq344535 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq344064
       have i₂ := eq340466
       grind)
    | exact superpose eq340466 eq344064
    | exact resolve eq344064 eq340466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344064
  have eq346561 : ∀ X0 X2 : G, (M.op (M.op (M.op x (M.op x y)) X0) (M.op x (M.op x y))) = (M.op (M.op (M.op x (M.op x y)) X0) (M.op (M.op (M.op x (M.op x y)) X0) X2)) := by
    intro X0 X2
    first
    | exact superpose eq773 eq961
    | exact resolve eq961 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq961
  have eq349294 : ∀ X0 X2 : G, (M.op (M.op x X0) (M.op (M.op x X0) X2)) = (M.op (M.op x X0) x) := by
    intro X0 X2
    first
    | exact superpose eq344535 eq346561
    | exact resolve eq346561 eq344535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346561
  have eq349443 : ∀ X0 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq349294 X0 x
       have i₂ := eq1197 X0 x
       grind)
    | exact superpose eq1197 eq349294
    | exact resolve eq349294 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq349294
  have eq349525 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | exact superpose eq344535 eq349443
    | exact resolve eq349443 eq344535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349443
  have eq349567 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1290 x X0
       have i₂ := eq344335 x
       grind)
    | exact superpose eq344335 eq1290
    | (have j0 := eq1290 x X0
       grind)
    | exact resolve eq1290 eq344335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349568 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1289 x
       have i₂ := eq344335 x
       grind)
    | exact superpose eq344335 eq1289
    | (have j0 := eq1289 x
       grind)
    | exact resolve eq1289 eq344335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349627 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1626
       have i₂ := eq344335 y
       grind)
    | exact superpose eq344335 eq1626
    | exact resolve eq1626 eq344335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq349639 : x = (M.op y x) := by grind
  clear eq349627
  have eq349662 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq349568
       have i₂ := eq340466
       grind)
    | exact superpose eq340466 eq349568
    | exact resolve eq349568 eq340466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349568
  have eq349663 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq349662
  have eq349664 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq349567 X0
       have i₂ := eq340466
       grind)
    | exact superpose eq340466 eq349567
    | (have j0 := eq349567 X0
       grind)
    | exact resolve eq349567 eq340466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349567
  have eq349665 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq349664 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349664
  have eq349678 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq349663
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq349663
    | exact resolve eq349663 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349663
  have eq349679 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq349665 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq349665
    | (have j0 := eq349665 X0
       grind)
    | exact resolve eq349665 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349665
  have eq349735 : ∀ X0 : G, (M.op x x) = (M.op (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq52 y X0 x
       have i₂ := eq349639
       grind)
    | exact superpose eq349639 eq52
    | exact resolve eq52 eq349639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349740 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq57 y X0 x
       have i₂ := eq349639
       grind)
    | exact superpose eq349639 eq57
    | exact resolve eq57 eq349639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350234 : ∀ X0 : G, x = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq349740 X0
       have i₂ := eq349639
       grind)
    | exact superpose eq349639 eq349740
    | exact resolve eq349740 eq349639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349740
  have eq350238 : ∀ X0 : G, x = (M.op (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq349735 X0
       have i₂ := eq340466
       grind)
    | exact superpose eq340466 eq349735
    | exact resolve eq349735 eq340466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340466 eq349735
  have eq355158 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq349678 eq393
    | exact resolve eq393 eq349678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355635 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq349678 eq355158
    | exact resolve eq355158 eq349678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355158
  have eq367853 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) X2)) X0) (M.op (M.op (σ x) X0) X3)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq393 eq1175
    | exact resolve eq1175 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq1175
  have eq369687 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) X2)) X0) (M.op (M.op (σ x) X0) X3)) (σ x)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq355635 eq367853
    | exact resolve eq367853 eq355635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367853
  have eq370092 : ∀ X0 X1 X3 : G, (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (M.op (M.op (σ x) X0) X3)) (σ x)) := by
    intro X0 X1 X3
    first
    | exact superpose eq56 eq369687
    | exact resolve eq369687 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq369687
  have eq370394 : ∀ X0 X1 X3 : G, (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) (M.op (M.op (σ x) X0) X3)) (σ x)) := by
    intro X0 X1 X3
    first
    | exact superpose eq215 eq370092
    | exact resolve eq370092 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq370092
  have eq370615 : ∀ X0 X1 X3 : G, (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X3)) (σ x)) := by
    intro X0 X1 X3
    first
    | exact superpose eq355635 eq370394
    | exact resolve eq370394 eq355635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370394
  have eq370805 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq1196 eq370615
    | exact resolve eq370615 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370615
  have eq370949 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq355635 eq370805
    | exact resolve eq370805 eq355635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370805
  have eq371057 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq1196 eq370949
    | exact resolve eq370949 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq370949
  have eq371115 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq355635 eq371057
    | exact resolve eq371057 eq355635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355635 eq371057
  have eq375775 : (k x y) = (τ (M.op (σ y) (σ x))) := by
    first
    | exact superpose eq349679 eq61
    | exact resolve eq61 eq349679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq349679
  have eq375790 : (M.op y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq375775
       have i₂ := eq344335 y
       grind)
    | exact superpose eq344335 eq375775
    | exact resolve eq375775 eq344335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344335 eq375775
  have eq375814 : x = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq375790
       have i₂ := eq349639
       grind)
    | exact superpose eq349639 eq375790
    | exact resolve eq375790 eq349639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375790
  have eq375845 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq375814 eq15
    | exact resolve eq15 eq375814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375814
  have eq375891 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq375845
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq375845
    | exact resolve eq375845 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375845
  have eq375967 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ y) X0) X0) := by
    intro X0
    first
    | exact superpose eq375891 eq52
    | exact resolve eq52 eq375891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375972 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq375891 eq57
    | exact resolve eq57 eq375891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376484 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq375891 eq375972
    | exact resolve eq375972 eq375891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375972
  have eq376488 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) X0) := by
    intro X0
    first
    | exact superpose eq349678 eq375967
    | exact resolve eq375967 eq349678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349678 eq375967
  have eq392859 : ∀ X0 X1 X3 : G, (k (M.op X0 (M.op X0 X1)) X3) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have j0 := eq983 X0 X1 x X3
       grind)
    | (have r₁ := eq983 X0 X1 x X3
       have r₂ := eq715 X0 X1 x X1
       grind)
    | exact resolve eq983 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq983
  have eq579033 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq349525 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq349525
    | (have j0 := eq349525 y
       grind)
    | exact resolve eq349525 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349525
  have eq581462 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq579033 eq14
    | exact resolve eq14 eq579033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581467 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | exact superpose eq579033 eq52
    | exact resolve eq52 eq579033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581889 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | exact superpose eq579033 eq581467
    | exact resolve eq581467 eq579033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581467
  have eq581891 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq579033 eq581462
    | exact resolve eq581462 eq579033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579033 eq581462
  have eq582742 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | exact superpose eq581889 eq514
    | exact resolve eq514 eq581889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583270 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq581889 eq582742
    | exact resolve eq582742 eq581889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581889 eq582742
  have eq597111 : ∀ X1 : G, (k (M.op x y) X1) = (M.op X1 (M.op x y)) := by
    intro X1
    first
    | exact superpose eq581891 eq392859
    | exact resolve eq392859 eq581891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581891
  have eq606224 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq597111 eq1290
    | (have j0 := eq1290 (M.op x y) X0
       grind)
    | exact resolve eq1290 eq597111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606225 : (σ (M.op x y)) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq597111 eq1289
    | (have j0 := eq1289 (M.op x y)
       grind)
    | exact resolve eq1289 eq597111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq606263 : (k (σ (M.op x y)) (σ y)) = (σ (M.op y (M.op x y))) := by
    first
    | exact superpose eq597111 eq130
    | exact resolve eq130 eq597111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq606292 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq583270 eq606225
    | exact resolve eq606225 eq583270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606225
  have eq606293 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq606292
  have eq606294 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq583270 eq606224
    | (have j0 := eq606224 X0
       grind)
    | exact resolve eq606224 eq583270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606224
  have eq606295 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq606294 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606294
  have eq606313 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq606293
    | exact resolve eq606293 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606293
  have eq606314 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq606295
    | (have j0 := eq606295 X0
       grind)
    | exact resolve eq606295 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606295
  have eq606372 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq606313 eq52
    | exact resolve eq52 eq606313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606887 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq606313 eq606372
    | exact resolve eq606372 eq606313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606372
  have eq606909 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq371115
    | (have j0 := eq371115 (σ y)
       grind)
    | exact resolve eq371115 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371115
  have eq609377 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq606909 eq14
    | exact resolve eq14 eq606909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609382 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq606909 eq52
    | exact resolve eq52 eq606909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609813 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq606909 eq609382
    | exact resolve eq609382 eq606909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609382
  have eq609815 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq606909 eq609377
    | exact resolve eq609377 eq606909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606909 eq609377
  have eq610231 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq609813 eq514
    | exact resolve eq514 eq609813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610771 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq609813 eq610231
    | exact resolve eq610231 eq609813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610231
  have eq611829 : ∀ X1 : G, (k (M.op (σ x) (σ y)) X1) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq609815 eq392859
    | exact resolve eq392859 eq609815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392859 eq609815
  have eq612932 : ∀ X0 : G, (σ (M.op (σ x) (σ y))) ≠ (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (k (σ (M.op (σ x) (σ y))) X0) = (M.op X0 (σ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq611829 eq1290
    | (have j0 := eq1290 (M.op (σ x) (σ y)) X0
       grind)
    | exact resolve eq1290 eq611829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq612964 : ∀ X0 : G, (σ (M.op (σ x) (σ y))) ≠ (σ (M.op (σ x) (σ y))) ∨ (k (σ (M.op (σ x) (σ y))) X0) = (M.op X0 (σ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq610771 eq612932
    | (have j0 := eq612932 X0
       grind)
    | exact resolve eq612932 eq610771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610771 eq612932
  have eq612965 : ∀ X0 : G, (k (σ (M.op (σ x) (σ y))) X0) = (M.op X0 (σ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq612964 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612964
  have eq613009 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq606314 eq37
    | exact resolve eq37 eq606314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq613037 : ∀ X0 : G, (M.op (σ X0) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq597111 eq613009
    | exact resolve eq613009 eq597111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613009
  have eq617051 : (M.op (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) := by
    first
    | exact superpose eq606314 eq606263
    | exact resolve eq606263 eq606314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606263
  have eq630389 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (τ X0)) = (τ (M.op X0 (σ (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq612965 eq345
    | exact resolve eq345 eq612965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq630424 : (σ (k (M.op (σ x) (σ y)) y)) = (M.op (σ y) (σ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq612965 eq40
    | exact resolve eq40 eq612965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq612965
  have eq630425 : (M.op (σ y) (σ (M.op (σ x) (σ y)))) = (σ (M.op y (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq611829 eq630424
    | exact resolve eq630424 eq611829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630424
  have eq630438 : ∀ X0 : G, (M.op (τ X0) (M.op (σ x) (σ y))) = (τ (M.op X0 (σ (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq611829 eq630389
    | exact resolve eq630389 eq611829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630389
  have eq633861 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ y) (σ (M.op y (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq630425 eq57
    | exact resolve eq57 eq630425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630425
  have eq634514 : (σ x) = (M.op (σ y) (σ (M.op y (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq376484 eq633861
    | exact resolve eq633861 eq376484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633861
  have eq635187 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ y) X1)) X0) = (M.op (M.op (σ y) X0) (M.op (M.op (σ y) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq634514 eq1122
    | exact resolve eq1122 eq634514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634514
  have eq635397 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ y) X1)) X0) = (M.op (M.op (σ y) X0) (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq375891 eq635187
    | exact resolve eq635187 eq375891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375891 eq635187
  have eq635733 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq376484 eq635397
    | exact resolve eq635397 eq376484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635397
  have eq810825 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (M.op (σ x) (σ y)) (σ (M.op (σ x) (σ y))))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq609813 eq630438
    | exact resolve eq630438 eq609813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609813
  have eq811030 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq630438 eq810825
    | exact resolve eq810825 eq630438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630438 eq810825
  have eq811135 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq811030
       have i₂ := eq52 (τ sF4) sF4 x
       grind)
    | (have i₁ := eq811030
       have i₂ := eq52 (τ sF4) x sF4
       grind)
    | exact superpose eq52 eq811030
    | exact resolve eq811030 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811030
  have eq816817 : ∀ X0 : G, (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X0) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq811135 eq514
    | exact resolve eq514 eq811135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq817361 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq811135 eq816817
    | exact resolve eq816817 eq811135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811135 eq816817
  have eq817532 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (k (τ (M.op (σ x) (σ y))) X0) = (M.op X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq817361 eq13
    | (have j0 := eq13 (τ (M.op (σ x) (σ y))) X0
       grind)
    | (have r₁ := eq13 (τ (M.op (σ x) (σ y))) x
       have r₂ := eq817361
       grind)
    | exact resolve eq13 eq817361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817361
  have eq817909 : ∀ X0 : G, (k (τ (M.op (σ x) (σ y))) X0) = (M.op X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq817532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817532
  have eq835606 : (τ (k (M.op (σ x) (σ y)) (σ y))) = (M.op y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq817909 eq827
    | exact resolve eq827 eq817909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq817909
  have eq835611 : (τ (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq611829 eq835606
    | exact resolve eq835606 eq611829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611829 eq835606
  have eq844716 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op y (τ (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq835611 eq57
    | exact resolve eq57 eq835611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835611
  have eq845370 : x = (M.op y (τ (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq844716 x
       have i₂ := eq350234 x
       grind)
    | exact superpose eq350234 eq844716
    | exact resolve eq844716 eq350234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844716
  have eq846338 : ∀ X0 X1 : G, (M.op (M.op y (M.op y X1)) X0) = (M.op (M.op y X0) (M.op (M.op y x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq845370 eq1122
    | exact resolve eq1122 eq845370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122 eq845370
  have eq846550 : ∀ X0 X1 : G, (M.op (M.op y (M.op y X1)) X0) = (M.op (M.op y X0) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq846338 X0 X1
       have i₂ := eq349639
       grind)
    | exact superpose eq349639 eq846338
    | exact resolve eq846338 eq349639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846338
  have eq846893 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y X0) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq846550 X0 x
       have i₂ := eq350234 x
       grind)
    | exact superpose eq350234 eq846550
    | exact resolve eq846550 eq350234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846550
  have eq1823089 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq635733
    | (have j0 := eq635733 (σ y)
       grind)
    | exact resolve eq635733 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635733
  have eq1826253 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X0)) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1823089 eq57
    | exact resolve eq57 eq1823089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1826978 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1823089 eq1826253
    | exact resolve eq1826253 eq1823089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823089 eq1826253
  have eq2040732 : (M.op x y) = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq846893 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq846893
    | (have j0 := eq846893 y
       grind)
    | exact resolve eq846893 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq846893
  have eq2062133 : (σ (k (M.op x y) (k y y))) = (M.op (k (σ y) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq606314 eq127
    | exact resolve eq127 eq606314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq606314
  have eq2062134 : (M.op (k (σ y) (σ y)) (σ (M.op x y))) = (σ (M.op (k y y) (M.op x y))) := by
    first
    | exact superpose eq597111 eq2062133
    | exact resolve eq2062133 eq597111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597111 eq2062133
  have eq2062135 : (M.op (k (σ y) (σ y)) (σ (M.op x y))) = (σ (M.op (M.op y y) (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2062134
       have i₂ := eq95 y y
       grind)
    | exact superpose eq95 eq2062134
    | (have j1 := eq95 y y
       grind)
    | exact resolve eq2062134 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062134
  have eq2062400 : (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2040732 eq2062135
    | exact resolve eq2062135 eq2040732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040732 eq2062135
  have eq2062404 : (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2062400
    | exact resolve eq2062400 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062400
  have eq2083508 : (k (σ y) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq206 eq110
    | exact resolve eq110 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq206
  have eq2083509 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq344535 eq2083508
    | exact resolve eq2083508 eq344535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344535 eq2083508
  have eq2083510 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2083509
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2083509
    | exact resolve eq2083509 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083509
  have eq2083514 : (τ (σ x)) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2083510 eq94
    | exact resolve eq94 eq2083510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq2083510
  have eq2083544 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq28 eq2083514
    | exact resolve eq2083514 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083514
  have eq2083627 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op y X0) X0) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2083544 eq52
    | exact resolve eq52 eq2083544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083544
  have eq2084322 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq2083627 x
       have i₂ := eq350238 x
       grind)
    | exact superpose eq350238 eq2083627
    | exact resolve eq2083627 eq350238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350238 eq2083627
  have eq2084627 : x = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq583270 eq2084322
    | exact resolve eq2084322 eq583270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583270 eq2084322
  have eq2085036 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2084627 eq1279
    | (have j0 := eq1279 y (M.op x y) x
       grind)
    | exact resolve eq1279 eq2084627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279 eq2084627
  have eq2085055 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq2085036
    | (have j0 := eq2085036 X0
       grind)
    | exact resolve eq2085036 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085036
  have eq2085082 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq606887 eq2085055
    | exact resolve eq2085055 eq606887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606887 eq2085055
  have eq2085105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2085082
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2085082
    | exact resolve eq2085082 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085082
  have eq2085125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2085105
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2085105
    | exact resolve eq2085105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085105
  have eq2085139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2085125
    | exact resolve eq2085125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085125
  have eq2085150 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2085139
       have r₂ := eq27
       grind)
    | exact resolve eq2085139 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085139
  have eq2085159 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2085150
    | exact resolve eq2085150 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085150
  have eq2085166 : (σ (M.op x y)) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq613037 eq2085159
    | exact resolve eq2085159 eq613037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613037 eq2085159
  have eq2085171 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq617051 eq2085166
    | exact resolve eq2085166 eq617051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085166
  have eq2086754 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ y) X0) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2085171 eq52
    | exact resolve eq52 eq2085171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2085171
  have eq2087448 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq376488 eq2086754
    | exact resolve eq2086754 eq376488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376488 eq2086754
  have eq2087750 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq606313 eq2087448
    | exact resolve eq2087448 eq606313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087448
  have eq2088170 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2087750 eq28
    | exact resolve eq28 eq2087750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2087750
  have eq2088803 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2088170
    | exact resolve eq2088170 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2088170
  have eq2088804 : x = (M.op x y) := by grind
  clear eq2088803
  have eq2089042 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2088804 eq20
    | exact resolve eq20 eq2088804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2089135 : (σ (M.op y x)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2088804 eq617051
    | exact resolve eq617051 eq2088804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617051 eq2088804
  have eq2089270 : (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2089135
       have i₂ := eq349639
       grind)
    | exact superpose eq349639 eq2089135
    | exact resolve eq2089135 eq349639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349639 eq2089135
  have eq2089344 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2089042
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2089042
    | exact resolve eq2089042 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089042
  have eq2089359 : (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2089270
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2089270
    | exact resolve eq2089270 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089270
  have eq2089513 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2089344 eq26
    | exact resolve eq26 eq2089344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2090503 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2089344 eq2089359
    | exact resolve eq2089359 eq2089344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089359
  have eq2090812 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ y) X1)) X0) = (M.op (M.op (σ y) X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq2090503 eq1115
    | exact resolve eq1115 eq2090503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq2090503
  have eq2091044 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ y) X1)) X0) = (M.op (M.op (σ y) X0) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq606313 eq2090812
    | exact resolve eq2090812 eq606313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090812
  have eq2091417 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq376484 eq2091044
    | exact resolve eq2091044 eq376484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091044
  have eq2091742 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ y) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2089344 eq2091417
    | exact resolve eq2091417 eq2089344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091417
  have eq2256049 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2062404
       have i₂ := eq95 sF3 sF3
       grind)
    | exact superpose eq95 eq2062404
    | (have j1 := eq95 (M.op (σ y) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq2062404 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq2062404
  have eq2256634 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2091742 eq2256049
    | exact resolve eq2256049 eq2091742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091742 eq2256049
  have eq2256693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2089513 eq2256634
    | exact resolve eq2256634 eq2089513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256634
  have eq2256702 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2256693
       have r₂ := eq27
       grind)
    | exact resolve eq2256693 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256693
  have eq2256860 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X1)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq2256702 eq717
    | exact resolve eq717 eq2256702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq2256702
  have eq2257253 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1826978 eq2256860
    | exact resolve eq2256860 eq1826978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826978 eq2256860
  have eq2257492 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq376484 eq2257253
    | exact resolve eq2257253 eq376484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376484 eq2257253
  have eq2257693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2089344 eq2257492
    | exact resolve eq2257492 eq2089344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257492
  have eq2257848 : y = (M.op y y) := by
    first
    | (have r₁ := eq2257693
       have r₂ := eq27
       grind)
    | exact resolve eq2257693 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257693
  have eq2258142 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq57 y X0 y
       have i₂ := eq2257848
       grind)
    | exact superpose eq2257848 eq57
    | exact resolve eq57 eq2257848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq2258756 : x = (M.op y y) := by
    first
    | (have i₁ := eq2258142 x
       have i₂ := eq350234 x
       grind)
    | exact superpose eq350234 eq2258142
    | exact resolve eq2258142 eq350234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350234 eq2258142
  have eq2258966 : x = y := by
    first
    | (have i₁ := eq2258756
       have i₂ := eq2257848
       grind)
    | exact superpose eq2257848 eq2258756
    | exact resolve eq2258756 eq2257848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257848 eq2258756
  have eq2259398 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2258966
       grind)
    | exact superpose eq2258966 eq24
    | exact resolve eq24 eq2258966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2258966
  have eq2259720 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2259398
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2259398
    | exact resolve eq2259398 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2259398
  have eq2259775 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2089344 eq2259720
    | exact resolve eq2259720 eq2089344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089344 eq2259720
  have eq2260189 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2259775 eq2089513
    | exact resolve eq2089513 eq2259775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089513 eq2259775
  have eq2260214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq606313 eq2260189
    | exact resolve eq2260189 eq606313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606313 eq2260189
  have eq2260416 : False := by grind
  exact eq2260416

/-- `Equation4438`: `x ◇ (y ◇ x) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_y_pxy_Equation4438 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4438 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4438.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X0) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq176 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X2) ∨ (k X0 (M.op X0 X2)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X1 X0))
       have r₂ := eq16 X0 X1 (M.op X1 X0)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq191 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op (M.op x y) x) x) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 (M.op x x)
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) x) := by
    first
    | (have i₁ := eq191 x
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq191
    | exact resolve eq191 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq211 : (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (M.op x (M.op (M.op x y) x)) = (k x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq192 eq13
    | (have j0 := eq13 x (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq13 x (M.op (M.op x y) x)
       have r₂ := eq192
       grind)
    | exact resolve eq13 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq214 : (M.op x (M.op (M.op x y) x)) = (k x (M.op (M.op x y) x)) := by grind
  clear eq211
  have eq215 : (M.op (M.op x y) x) = (k x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq214
       have i₂ := eq180 sF0
       grind)
    | exact superpose eq180 eq214
    | exact resolve eq214 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq413 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq601 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X2 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 y X0 x
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq182
    | (have j0 := eq182 (σ y) X0 (σ x)
       grind)
    | exact resolve eq182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq667 (M.op y x)
       have i₂ := eq16 y X0 x
       grind)
    | exact superpose eq16 eq667
    | exact resolve eq667 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op y X1) y) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq16 y x x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq16
    | (have j0 := eq16 y x X1
       grind)
    | exact resolve eq16 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : (M.op y (M.op x y)) = (M.op y (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq698 x
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq698 x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq698
    | (have j0 := eq698 x
       grind)
    | exact resolve eq698 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq720 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) (σ y)) := by
    intro X1
    first
    | exact superpose eq669 eq16
    | (have j0 := eq16 (σ y) (σ x) X1
       grind)
    | exact resolve eq16 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq28 (M.op (M.op X1 X1) X0) X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op X1 (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq801 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq815 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 (M.op X0 X1) X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 (M.op X0 X1) X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq822
       grind)
    | exact superpose eq822 eq41
    | exact resolve eq41 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq853
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq853
    | exact resolve eq853 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq856 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq854
    | exact resolve eq854 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq856 eq831
    | exact resolve eq831 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq866
       have r₂ := eq27
       grind)
    | exact resolve eq866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq878 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq873 eq720
    | exact resolve eq720 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq873 eq669
    | exact resolve eq669 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (M.op (σ y) X0) ∨ (σ y) = (k X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq873 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq873
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq873
       grind)
    | exact resolve eq12 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq873 eq13
    | exact resolve eq13 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq873 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq881
       have r₂ := eq883
       grind)
    | exact resolve eq881 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq883
  have eq894 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq878
    | exact resolve eq878 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq899 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq893 eq116
    | exact resolve eq116 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq906 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq899
    | exact resolve eq899 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq911 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq894 eq720
    | exact resolve eq720 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq894 eq177
    | exact resolve eq177 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq919 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq720 eq916
    | exact resolve eq916 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq922 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq879 eq919
    | exact resolve eq919 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq919
  have eq925 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq911 eq922
    | exact resolve eq922 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq940 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq911 eq177
    | exact resolve eq177 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq949 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq925 eq181
    | exact resolve eq181 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq925 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq952 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq925 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq950
    | exact resolve eq950 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq856 eq962
    | exact resolve eq962 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq972 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq967
       have r₂ := eq27
       grind)
    | exact resolve eq967 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq1117 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq952 eq115
    | exact resolve eq115 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq952
  have eq1493 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq880 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq1494 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq856 eq1493
    | exact resolve eq1493 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq1493
  have eq1498 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1494 eq925
    | exact resolve eq925 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq1511 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1498
  have eq1524 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1511
       have r₂ := eq972
       grind)
    | exact resolve eq1511 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq1511
  have eq1534 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq704 y
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq704
    | exact resolve eq704 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1535 : (M.op y x) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq667 y
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq667
    | exact resolve eq667 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1537 : x ≠ y ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq13
    | exact resolve eq13 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1539 : x = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq28
    | exact resolve eq28 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1543 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq178 y y X0
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq178
    | exact resolve eq178 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1548 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1543 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1543
    | (have j0 := eq1543 X0
       grind)
    | exact resolve eq1543 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1553 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1537
       have r₂ := eq1539
       grind)
    | exact resolve eq1537 eq1539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq1539
  have eq1554 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1534
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1534
    | exact resolve eq1534 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1556 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1548 x
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq1548 x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq1548
    | (have j0 := eq1548 x
       grind)
    | exact resolve eq1548 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1561 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1554 eq1556
    | exact resolve eq1556 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1563 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq41
    | exact resolve eq41 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1566 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1563
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1563
    | exact resolve eq1563 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq1568 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1566
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1566
    | exact resolve eq1566 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1593 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1561 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq1561
       grind)
    | exact resolve eq13 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq1602 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1593
  have eq1604 : (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1554 eq1602
    | exact resolve eq1602 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1608 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1568 eq838
    | (have j0 := eq838 (σ y)
       grind)
    | exact resolve eq838 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1614 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1604 eq37
    | exact resolve eq37 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1617 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq1614
    | exact resolve eq1614 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq1833 : (σ y) = (k (σ (M.op y y)) (σ y)) ∨ y = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq840 y
       grind)
    | exact superpose eq840 eq41
    | (have j1 := eq840 y
       grind)
    | exact resolve eq41 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1842 : (σ y) = (k (σ (M.op y y)) (σ y)) ∨ y = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq1833
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1833
    | exact resolve eq1833 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1849 : (σ y) = (k (σ (M.op y y)) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1842
       have i₂ := eq667 y
       grind)
    | exact superpose eq667 eq1842
    | exact resolve eq1842 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq2138 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq801 y y X0
       have i₂ := eq906
       grind)
    | exact superpose eq906 eq801
    | (have j0 := eq801 y y x
       grind)
    | exact resolve eq801 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2236 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2138 x
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq2138 x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq2138
    | (have j0 := eq2138 x
       grind)
    | exact resolve eq2138 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138
  have eq2254 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2236
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2236
    | exact resolve eq2236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq2388 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2254 eq704
    | exact resolve eq704 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2418 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2388 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq2388
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq2388
       grind)
    | exact resolve eq13 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388
  have eq2428 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq2418
  have eq2434 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2254 eq2428
    | exact resolve eq2428 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254 eq2428
  have eq2439 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2434 eq37
    | exact resolve eq37 eq2434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2444 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2439
    | exact resolve eq2439 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq2447 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1524 eq2444
    | exact resolve eq2444 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2444
  have eq2450 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq893 eq2447
    | exact resolve eq2447 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447
  have eq2452 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2450
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq2450
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq2450 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2458 : y ≠ y ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2450
       grind)
    | exact superpose eq2450 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq2450
       grind)
    | exact resolve eq13 eq2450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2467 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq2450
  have eq2468 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq2458
  have eq2475 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq906 eq2468
    | exact resolve eq2468 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468
  have eq2479 : (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq838 y
       grind)
    | (have r₁ := eq2452
       have r₂ := eq838 y
       grind)
    | exact resolve eq2452 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq2452
  have eq2485 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2475
       have r₂ := eq2467
       grind)
    | exact resolve eq2475 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467 eq2475
  have eq2486 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq906 eq2479
    | exact resolve eq2479 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2489 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq704 y
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq704
    | exact resolve eq704 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2490 : (M.op y x) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq667 y
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq667
    | exact resolve eq667 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2493 : x ≠ y ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq13
    | exact resolve eq13 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2499 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq178 y y X0
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq178
    | exact resolve eq178 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2507 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2499 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2499
    | (have j0 := eq2499 X0
       grind)
    | exact resolve eq2499 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499
  have eq2512 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2493
       have r₂ := eq2486
       grind)
    | exact resolve eq2493 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486 eq2493
  have eq2513 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2489
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2489
    | exact resolve eq2489 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2489
  have eq2515 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2507 x
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq2507 x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq2507
    | (have j0 := eq2507 x
       grind)
    | exact resolve eq2507 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq2520 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2513 eq2515
    | exact resolve eq2515 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515
  have eq2523 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2512
       grind)
    | exact superpose eq2512 eq41
    | exact resolve eq41 eq2512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq2528 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2523
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2523
    | exact resolve eq2523 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523
  have eq2531 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2528
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2528
    | exact resolve eq2528 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528
  have eq2559 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2520 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq2520
       grind)
    | exact resolve eq13 eq2520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520
  have eq2569 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq2559
  have eq2571 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2513 eq2569
    | exact resolve eq2569 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569
  have eq2577 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2531 eq801
    | (have j0 := eq801 (σ y) (σ y) x
       grind)
    | exact resolve eq801 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2579 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq669 eq2577
    | (have j0 := eq2577 (σ x)
       grind)
    | exact resolve eq2577 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq2583 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq2579
    | exact resolve eq2579 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq2586 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2571 eq37
    | exact resolve eq37 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2591 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq2586
    | exact resolve eq2586 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586
  have eq2598 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2591 eq801
    | (have j0 := eq801 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq801 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2599 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq669 eq2598
    | (have j0 := eq2598 (σ x)
       grind)
    | exact resolve eq2598 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq3551 : ∀ X0 : G, (M.op y x) = (k (M.op y X0) y) ∨ x = (M.op y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq815 y x y
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq815
    | exact resolve eq815 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3553 : ∀ X0 : G, (M.op y x) = (k (M.op y X0) y) ∨ x = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq815 y x y
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq815
    | exact resolve eq815 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq3579 : ∀ X0 : G, (M.op (σ y) (σ x)) = (k (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ y) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq873 eq815
    | exact resolve eq815 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3710 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ y) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq925 eq3579
    | (have j0 := eq3579 X0
       grind)
    | exact resolve eq3579 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3721 : ∀ X0 : G, (M.op y (M.op x y)) = (k (M.op y X0) y) ∨ x = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1535 eq3553
    | (have j0 := eq3553 X0
       grind)
    | exact resolve eq3553 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535 eq3553
  have eq3722 : ∀ X0 : G, (M.op y (M.op x y)) = (k (M.op y X0) y) ∨ x = (M.op y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2490 eq3551
    | (have j0 := eq3551 X0
       grind)
    | exact resolve eq3551 eq2490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2490 eq3551
  have eq3740 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) X0) (σ x)) ∨ (σ x) = (M.op (σ y) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2485 eq3710
    | (have j0 := eq3710 X0
       grind)
    | exact resolve eq3710 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3710
  have eq3746 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ x = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1554 eq3721
    | (have j0 := eq3721 X0
       grind)
    | exact resolve eq3721 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721
  have eq3747 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ x = (M.op y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2513 eq3722
    | (have j0 := eq3722 X0
       grind)
    | exact resolve eq3722 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3722
  have eq3752 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) X0) (σ x)) ∨ (σ x) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2485 eq3740
    | (have j0 := eq3740 X0
       grind)
    | exact resolve eq3740 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740
  have eq4132 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1554 eq3746
    | exact resolve eq3746 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554 eq3746
  have eq4154 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4132
  have eq4185 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4154 eq41
    | exact resolve eq41 eq4154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4154
  have eq4192 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq4185
    | exact resolve eq4185 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4185
  have eq4199 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4192 eq799
    | (have j0 := eq799 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq799 (σ (M.op x y)) (σ y)
       have r₂ := eq4192
       grind)
    | exact resolve eq799 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4201 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4199
  have eq4202 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1617 eq4201
    | exact resolve eq4201 eq1617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617 eq4201
  have eq4217 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2513 eq3747
    | exact resolve eq3747 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513 eq3747
  have eq4241 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq4217
  have eq4274 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4241 eq41
    | exact resolve eq41 eq4241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4241
  have eq4281 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq4274
    | exact resolve eq4274 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274
  have eq4288 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4281 eq799
    | (have j0 := eq799 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq799 (σ (M.op x y)) (σ y)
       have r₂ := eq4281
       grind)
    | exact resolve eq799 eq4281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4290 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq4288
  have eq4291 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2591 eq4290
    | exact resolve eq4290 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591 eq4290
  have eq4751 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4202 eq669
    | exact resolve eq669 eq4202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4752 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4202 eq840
    | exact resolve eq840 eq4202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4756 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4202 eq28
    | exact resolve eq28 eq4202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4758 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4202 eq176
    | exact resolve eq176 eq4202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4769 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq4756
  have eq4779 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq720 eq4758
    | exact resolve eq4758 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4758
  have eq4781 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1568 eq4769
    | exact resolve eq4769 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568 eq4769
  have eq4783 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4192 eq4752
    | exact resolve eq4752 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4752
  have eq4784 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq4783
  have eq4791 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4751 eq4779
    | exact resolve eq4779 eq4751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4751 eq4779
  have eq4794 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4781 eq4784
    | exact resolve eq4784 eq4781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq4800 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4781 eq4791
    | exact resolve eq4791 eq4781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4781 eq4791
  have eq4807 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4794 eq4800
    | exact resolve eq4800 eq4794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4794 eq4800
  have eq4934 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4807 eq4202
    | exact resolve eq4202 eq4807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4202 eq4807
  have eq4957 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq4934
  have eq4972 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4957 eq720
    | exact resolve eq720 eq4957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5000 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4972 eq28
    | (have j0 := eq28 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq28 eq4972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5024 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4192 eq5000
    | exact resolve eq5000 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5000
  have eq5645 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (k X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1 (M.op X1 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6122 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4291 eq720
    | exact resolve eq720 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291
  have eq6168 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4972 eq6122
    | exact resolve eq6122 eq4972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6122
  have eq6191 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2583 eq6168
    | exact resolve eq6168 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583 eq6168
  have eq6500 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5024 eq720
    | exact resolve eq720 eq5024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024
  have eq6902 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6500 eq840
    | exact resolve eq840 eq6500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6500
  have eq6945 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4192 eq6902
    | exact resolve eq6902 eq4192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192 eq6902
  have eq6946 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6945
  have eq6961 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4957 eq6946
    | exact resolve eq6946 eq4957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957 eq6946
  have eq6962 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6961
  have eq6985 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6962 eq4972
    | exact resolve eq4972 eq6962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4972
  have eq6986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6962 eq6191
    | exact resolve eq6191 eq6962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191 eq6962
  have eq7008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6986
  have eq7009 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6985
  have eq7028 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq7008
       have r₂ := eq1608
       grind)
    | exact resolve eq7008 eq1608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608 eq7008
  have eq7035 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq7028
       have r₂ := eq27
       grind)
    | exact resolve eq7028 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7028
  have eq7125 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7035 eq669
    | exact resolve eq669 eq7035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7169 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7009 eq7125
    | exact resolve eq7125 eq7009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7009 eq7125
  have eq7177 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7035 eq7169
    | exact resolve eq7169 eq7035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7035 eq7169
  have eq7178 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7177
  have eq7192 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7178 eq29
    | exact resolve eq29 eq7178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq7205 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7178 eq4281
    | exact resolve eq4281 eq7178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281 eq7178
  have eq7223 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq7205
  have eq7228 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2531 eq7223
    | exact resolve eq7223 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531 eq7223
  have eq7229 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7228
  have eq7243 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq7192
    | exact resolve eq7192 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7192
  have eq7250 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7229 eq32
    | exact resolve eq32 eq7229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7229
  have eq7394 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq7250
    | exact resolve eq7250 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7250
  have eq7425 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7243 eq7394
    | exact resolve eq7394 eq7243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7243 eq7394
  have eq7426 : x = (M.op x y) := by grind
  clear eq7425
  have eq7438 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq18
    | exact resolve eq18 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7439 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq22
    | exact resolve eq22 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7440 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq36
    | exact resolve eq36 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq7441 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq40
    | exact resolve eq40 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq7442 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq180
    | exact resolve eq180 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq7443 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq185
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq185
    | (have r₁ := eq185
       have r₂ := eq7426
       grind)
    | exact resolve eq185 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq7446 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq215
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq215
    | exact resolve eq215 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq7447 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq822
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq822
    | exact resolve eq822 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq7449 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1117
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq1117
    | exact resolve eq1117 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq7464 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
  clear eq7443
  have eq7470 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7439 eq20
    | exact resolve eq20 eq7439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7481 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq7439 eq413
    | exact resolve eq413 eq7439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7509 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7470 eq2599
    | exact resolve eq2599 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2599
  have eq7530 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq7509
    | exact resolve eq7509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7509
  have eq7568 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k X0 (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq7438 eq800
    | (have j0 := eq800 (M.op (M.op x y) (k X0 (M.op x y))) (M.op x y) x
       grind)
    | exact resolve eq800 eq7438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq7723 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq873 eq601
    | exact resolve eq601 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq7886 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq26 eq7723
    | (have j0 := eq7723 X0
       grind)
    | exact resolve eq7723 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7723
  have eq7943 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq720 eq7886
    | exact resolve eq7886 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7886
  have eq7977 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq7943
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq7943
    | exact resolve eq7943 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq8101 : (k y (M.op x y)) = (M.op y (k y (M.op x y))) := by
    first
    | exact superpose eq7464 eq711
    | exact resolve eq711 eq7464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq8106 : (k y (M.op x y)) = (M.op (k y (M.op x y)) y) := by
    first
    | exact superpose eq7464 eq704
    | exact resolve eq704 eq7464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq8119 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op (M.op x y) (k y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq7464 eq182
    | exact resolve eq182 eq7464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq8129 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k y (M.op x y))) := by
    first
    | exact superpose eq7442 eq8119
    | exact resolve eq8119 eq7442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7442 eq8119
  have eq8370 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2434 eq7441
    | exact resolve eq7441 eq2434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2434
  have eq8417 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq8370
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8370
    | exact resolve eq8370 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8370
  have eq8439 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq8417
    | exact resolve eq8417 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8417
  have eq8447 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7470 eq8439
    | exact resolve eq8439 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8439
  have eq8453 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8447
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq8447
    | exact resolve eq8447 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8447
  have eq8648 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq7446 eq7440
    | exact resolve eq7440 eq7446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7440 eq7446
  have eq8821 : ∀ X0 : G, (M.op y (M.op y (M.op X0 y))) = (M.op (k y (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq8101 eq176
    | exact resolve eq176 eq8101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq8823 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (k y (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq8101 eq177
    | exact resolve eq177 eq8101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8834 : ∀ X0 : G, (M.op y (M.op X0 y)) = (k (k y (M.op x y)) y) ∨ (k y (M.op x y)) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq8101 eq815
    | exact resolve eq815 eq8101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8101
  have eq8836 : (M.op y (M.op x y)) = (k (k y (M.op x y)) y) ∨ (k y (M.op x y)) = (M.op y y) := by
    first
    | (have i₁ := eq8834 x
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq8834 x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq8834
    | (have j0 := eq8834 x
       grind)
    | exact resolve eq8834 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8834
  have eq8842 : ∀ X0 : G, (k y (M.op x y)) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | exact superpose eq8106 eq8823
    | exact resolve eq8823 eq8106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8823
  have eq8844 : ∀ X0 : G, (k y (M.op x y)) = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq8106 eq8821
    | exact resolve eq8821 eq8106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8106 eq8821
  have eq8853 : (k y (M.op x y)) = (k (k y (M.op x y)) y) ∨ (k y (M.op x y)) = (M.op y y) := by
    first
    | exact superpose eq7464 eq8836
    | exact resolve eq8836 eq7464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8836
  have eq8857 : ∀ X0 : G, (k y (M.op x y)) = (k y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq8844 X0
       have i₂ := eq5645 y X0
       grind)
    | exact superpose eq5645 eq8844
    | exact resolve eq8844 eq5645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5645 eq8844
  have eq8860 : (k y (M.op x y)) = (k y (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq8857 x
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq8857 x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq8857
    | (have j0 := eq8857 x
       grind)
    | exact resolve eq8857 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq8857
  have eq8863 : (k y (M.op x y)) = (k y (k y (M.op x y))) := by
    first
    | exact superpose eq7464 eq8860
    | exact resolve eq8860 eq7464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8860
  have eq8918 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (k y (M.op x y)) (M.op x y)) = (M.op (k y (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq8129 eq13
    | (have j0 := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq13 eq8129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8129
  have eq9198 : (σ (k y (M.op x y))) = (k (σ y) (σ (k y (M.op x y)))) := by
    first
    | exact superpose eq8863 eq37
    | exact resolve eq37 eq8863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8863
  have eq9203 : (k (σ y) (σ (M.op x y))) = (k (σ y) (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq42 eq9198
    | exact resolve eq9198 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9198
  have eq9204 : (k (σ y) (σ x)) = (k (σ y) (k (σ y) (σ x))) := by
    first
    | exact superpose eq7470 eq9203
    | exact resolve eq9203 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9203
  have eq9205 : (k (σ y) (σ x)) = (k (σ y) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq9204
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9204
    | exact resolve eq9204 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9204
  have eq9583 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq925 eq662
    | exact resolve eq662 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq925
  have eq9786 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq181 eq9583
    | exact resolve eq9583 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9583
  have eq9866 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq9786
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq9786
    | exact resolve eq9786 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9786
  have eq9930 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1849
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq1849
    | exact resolve eq1849 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9941 : (τ (σ y)) = (k (M.op y y) (τ (σ y))) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1849 eq413
    | exact resolve eq413 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq1849
  have eq9954 : y = (k (M.op y y) y) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq32 eq9941
    | exact resolve eq9941 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9941
  have eq9958 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9930
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9930
    | exact resolve eq9930 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9930
  have eq9962 : y = (k (M.op y y) y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq7464 eq9954
    | exact resolve eq9954 eq7464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9954
  have eq9966 : y = (k y (M.op x y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7464 eq9958
    | exact resolve eq9958 eq7464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7464 eq9958
  have eq9970 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2571 eq9966
    | exact resolve eq9966 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571 eq9966
  have eq10061 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq7447 eq41
    | exact resolve eq41 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10067 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq10061
    | exact resolve eq10061 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10061
  have eq10071 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq7470 eq10067
    | exact resolve eq10067 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10067
  have eq10093 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq10071 eq831
    | exact resolve eq831 eq10071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10544 : y = (k (k y y) y) ∨ y = (k y (M.op x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9962
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq9962
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq9962 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10554 : (σ y) = (k (σ (M.op y y)) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq9962
       grind)
    | exact superpose eq9962 eq41
    | exact resolve eq41 eq9962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9962
  have eq10555 : (σ y) = (k (σ (M.op y y)) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq10554
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10554
    | exact resolve eq10554 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10554
  have eq10578 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq7977 eq940
    | exact resolve eq940 eq7977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq10581 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq7977 eq16
    | exact resolve eq16 eq7977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10586 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq7977 eq177
    | exact resolve eq177 eq7977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq7977
  have eq10608 : (M.op x y) = (M.op y y) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10578
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq10578
    | exact resolve eq10578 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10578
  have eq10609 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq10608
  have eq10887 : (σ y) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10555
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq10555
    | exact resolve eq10555 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485
  have eq10913 : (σ y) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10887
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10887
    | exact resolve eq10887 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10887
  have eq10918 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9970 eq10913
    | exact resolve eq10913 eq9970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10913
  have eq10927 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10918 eq10071
    | exact resolve eq10071 eq10918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10071 eq10918
  have eq10933 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq10927
  have eq11521 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq10093 eq720
    | exact resolve eq720 eq10093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11522 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq10093 eq669
    | exact resolve eq669 eq10093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11565 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq11521
    | exact resolve eq11521 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11521
  have eq11581 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10933 eq7441
    | exact resolve eq7441 eq10933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10933
  have eq11591 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq11581
    | exact resolve eq11581 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11581
  have eq11597 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7470 eq11591
    | exact resolve eq11591 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11591
  have eq11741 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq11565 eq720
    | exact resolve eq720 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11827 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11597 eq799
    | (have j0 := eq799 (σ x) (σ x)
       grind)
    | (have r₁ := eq799 (σ x) (σ x)
       have r₂ := eq11597
       grind)
    | exact resolve eq799 eq11597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11597
  have eq11829 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq11827
  have eq11830 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq11829
  have eq11949 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq11741 eq28
    | (have j0 := eq28 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq28 eq11741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11741
  have eq11972 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq10093 eq11949
    | exact resolve eq11949 eq10093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10093 eq11949
  have eq11973 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq11972
  have eq15847 : (τ (σ x)) = (k y (τ (σ x))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8453 eq108
    | exact resolve eq108 eq8453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq8453
  have eq15856 : x = (k y x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq15847
    | exact resolve eq15847 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15847
  have eq15868 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15856
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq15856
    | exact resolve eq15856 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15856
  have eq15996 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq11522 eq11565
    | exact resolve eq11565 eq11522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11522
  have eq16020 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq15996
  have eq16053 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq16020 eq181
    | exact resolve eq181 eq16020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16020
  have eq16300 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ≠ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq10581 eq184
    | exact resolve eq184 eq10581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq16363 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq16300 x
       have r₂ := eq10581 x
       grind)
    | exact resolve eq16300 eq10581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16300
  have eq16407 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq10581 eq16363
    | exact resolve eq16363 eq10581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10581 eq16363
  have eq16418 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq10609 eq16407
    | exact resolve eq16407 eq10609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16407
  have eq16704 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq949 eq10586
    | exact resolve eq10586 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949 eq10586
  have eq16823 : (M.op x y) = (M.op y y) ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16704
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq16704
    | exact resolve eq16704 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16704
  have eq16824 : (M.op x y) = (M.op y y) ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by grind
  clear eq16823
  have eq16832 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq10609 eq16824
    | exact resolve eq16824 eq10609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10609 eq16824
  have eq18279 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq7449 eq7441
    | exact resolve eq7441 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7441
  have eq18287 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18279
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq18279
    | exact resolve eq18279 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18279
  have eq18310 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18287
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18287
    | exact resolve eq18287 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18287
  have eq18455 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq18310 eq9205
    | exact resolve eq9205 eq18310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9205
  have eq18884 : (σ (k y (M.op x y))) = (k (σ (k y (M.op x y))) (σ y)) ∨ (k y (M.op x y)) = (M.op y y) := by
    first
    | exact superpose eq8853 eq41
    | exact resolve eq41 eq8853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8853
  have eq18896 : (k (σ y) (σ (M.op x y))) = (k (k (σ y) (σ (M.op x y))) (σ y)) ∨ (k y (M.op x y)) = (M.op y y) := by
    first
    | exact superpose eq42 eq18884
    | exact resolve eq18884 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq18884
  have eq18901 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (σ y)) ∨ (k y (M.op x y)) = (M.op y y) := by
    first
    | exact superpose eq7470 eq18896
    | exact resolve eq18896 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18896
  have eq18904 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (σ y)) ∨ (k y (M.op x y)) = (M.op y y) := by
    first
    | (have i₁ := eq18901
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18901
    | exact resolve eq18901 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18901
  have eq19214 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (k y (M.op x y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq18310 eq18904
    | exact resolve eq18904 eq18310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18310 eq18904
  have eq19239 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq7449 eq19214
    | exact resolve eq19214 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7449 eq19214
  have eq19246 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (τ (σ x)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq11973 eq19239
    | exact resolve eq19239 eq11973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11973 eq19239
  have eq19252 : x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq30 eq19246
    | exact resolve eq19246 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19246
  have eq19255 : (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq19252
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq19252
    | exact resolve eq19252 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19252
  have eq19256 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq19255
  have eq19266 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19256 eq799
    | (have j0 := eq799 (M.op (σ x) (σ y)) (σ y)
       grind)
    | (have r₁ := eq799 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq19256
       grind)
    | exact resolve eq799 eq19256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq19256
  have eq19268 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq19266
  have eq19269 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18455 eq19268
    | exact resolve eq19268 eq18455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18455 eq19268
  have eq19270 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7530 eq19269
    | exact resolve eq19269 eq7530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7530 eq19269
  have eq19271 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11565 eq19270
    | exact resolve eq19270 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11565 eq19270
  have eq19272 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11830 eq19271
    | exact resolve eq19271 eq11830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19271
  have eq19273 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11830 eq19272
    | exact resolve eq19272 eq11830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11830 eq19272
  have eq19274 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq19273
  have eq19286 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq19274 eq9866
    | exact resolve eq9866 eq19274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9866
  have eq19311 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq19286
  have eq19319 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19274 eq19311
    | exact resolve eq19311 eq19274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19274 eq19311
  have eq19577 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq3752
    | (have j0 := eq3752 (σ y)
       grind)
    | exact resolve eq3752 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19597 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (M.op (σ x) X1) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq3752 eq815
    | (have j0 := eq815 (σ x) X1 x
       have j1 := eq3752 X1
       grind)
    | exact resolve eq815 eq3752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq3752
  have eq19609 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) X1) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) X1) ∨ x = (M.op y y) := by
    intro X1
    first
    | exact superpose eq181 eq19597
    | (have j0 := eq19597 x X1
       grind)
    | exact resolve eq19597 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19597
  have eq19625 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19577
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq19577
    | exact resolve eq19577 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19577
  have eq19633 : ∀ X1 : G, (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) X1) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq19609 X1
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq19609
    | (have j0 := eq19609 X1
       grind)
    | exact resolve eq19609 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19609
  have eq19643 : ∀ X1 : G, (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | exact superpose eq19319 eq19633
    | (have j0 := eq19633 X1
       grind)
    | exact resolve eq19633 eq19319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19319 eq19633
  have eq19644 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have j0 := eq19643 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19643
  have eq19683 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq19644 eq181
    | (have j1 := eq19644 X0
       grind)
    | exact resolve eq181 eq19644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19644
  have eq19764 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq19683 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19683
  have eq20034 : y = (k x y) ∨ y = (k y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10544
       have i₂ := eq906
       grind)
    | exact superpose eq906 eq10544
    | exact resolve eq10544 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq10544
  have eq20066 : y = (k (M.op x y) y) ∨ y = (k y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq20034
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq20034
    | exact resolve eq20034 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20034
  have eq20073 : (M.op x y) = (M.op y y) ∨ y = (k (M.op x y) y) ∨ y = (k y (M.op x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20066
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq20066
    | exact resolve eq20066 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20066
  have eq20077 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7447 eq20073
    | exact resolve eq20073 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20073
  have eq20080 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15868 eq20077
    | exact resolve eq20077 eq15868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15868 eq20077
  have eq20081 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq20080
  have eq20090 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10555
       have i₂ := eq20081
       grind)
    | exact superpose eq20081 eq10555
    | exact resolve eq10555 eq20081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10555
  have eq20096 : (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8842 y
       have i₂ := eq20081
       grind)
    | exact superpose eq20081 eq8842
    | exact resolve eq8842 eq20081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20102 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq20081
       grind)
    | exact superpose eq20081 eq28
    | (have j0 := eq28 y y
       grind)
    | exact resolve eq28 eq20081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20081
  have eq20120 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq20102
  have eq20136 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7438 eq20096
    | exact resolve eq20096 eq7438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20096
  have eq20138 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq20090
    | exact resolve eq20090 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20090
  have eq20147 : (σ y) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7470 eq20138
    | exact resolve eq20138 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20138
  have eq20155 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20136 eq20147
    | exact resolve eq20147 eq20136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20136 eq20147
  have eq20156 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq20155
  have eq20178 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq20120
       grind)
    | exact superpose eq20120 eq41
    | exact resolve eq41 eq20120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq20120
  have eq20199 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20178
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20178
    | exact resolve eq20178 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20178
  have eq20203 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq20199
    | exact resolve eq20199 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20199
  have eq20206 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7470 eq20203
    | exact resolve eq20203 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20203
  have eq20208 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq893 eq20206
    | exact resolve eq20206 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq20206
  have eq20210 : y = (M.op x y) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20208
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq20208
    | exact resolve eq20208 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20208
  have eq20211 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20210
  have eq20224 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20211 eq801
    | (have j0 := eq801 (σ y) (σ y) x
       grind)
    | exact resolve eq801 eq20211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq20225 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq669 eq20224
    | (have j0 := eq20224 (σ x)
       grind)
    | exact resolve eq20224 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20224
  have eq20229 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq20225
    | exact resolve eq20225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20225
  have eq20287 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20156 eq831
    | exact resolve eq831 eq20156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq20156
  have eq20309 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq873 eq20287
    | exact resolve eq20287 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq20287
  have eq20315 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20309
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq20309
    | exact resolve eq20309 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20309
  have eq20316 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20315
  have eq20343 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20316 eq720
    | exact resolve eq720 eq20316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20344 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20316 eq669
    | exact resolve eq669 eq20316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq20345 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20316 eq840
    | exact resolve eq840 eq20316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq20316
  have eq20385 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9970 eq20345
    | exact resolve eq20345 eq9970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20345
  have eq20386 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq20343
    | exact resolve eq20343 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20343
  have eq20396 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9970 eq20385
    | exact resolve eq20385 eq9970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9970 eq20385
  have eq20567 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20229 eq720
    | exact resolve eq720 eq20229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq20229
  have eq20668 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20344 eq20386
    | exact resolve eq20386 eq20344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20344 eq20386
  have eq20694 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20668
  have eq20757 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20694 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq20694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20694
  have eq22454 : (τ (σ y)) = (k (M.op x y) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20396 eq7481
    | exact resolve eq7481 eq20396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7481 eq20396
  have eq22465 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq22454
    | exact resolve eq22454 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22454
  have eq22679 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22465 eq181
    | exact resolve eq181 eq22465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq22715 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22465 eq22679
    | exact resolve eq22679 eq22465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22465 eq22679
  have eq22781 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22715 eq16053
    | exact resolve eq16053 eq22715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16053 eq22715
  have eq22814 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq22781
  have eq22847 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22814
       have r₂ := eq19764
       grind)
    | exact resolve eq22814 eq19764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19764 eq22814
  have eq22868 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7447 eq22847
    | exact resolve eq22847 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7447 eq22847
  have eq22869 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq22868
  have eq22893 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22869 eq16832
    | exact resolve eq16832 eq22869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16832
  have eq22935 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq22893
  have eq22957 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22869 eq22935
    | exact resolve eq22935 eq22869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22869 eq22935
  have eq23028 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22957 eq16418
    | exact resolve eq16418 eq22957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16418 eq22957
  have eq23069 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq23028
  have eq23637 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23069 eq19625
    | exact resolve eq19625 eq23069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19625 eq23069
  have eq23645 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23637
  have eq23681 : (k y (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8842 y
       have i₂ := eq23645
       grind)
    | exact superpose eq23645 eq8842
    | exact resolve eq8842 eq23645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8842 eq23645
  have eq23721 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7438 eq23681
    | exact resolve eq23681 eq7438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23681
  have eq23760 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23721 eq37
    | exact resolve eq37 eq23721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq23768 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq23760
    | exact resolve eq23760 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23760
  have eq23775 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7470 eq23768
    | exact resolve eq23768 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23768
  have eq23830 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23775 eq20757
    | exact resolve eq20757 eq23775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20757 eq23775
  have eq23837 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23830
  have eq23983 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23837 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq23837
       grind)
    | exact resolve eq13 eq23837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23985 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23837 eq28
    | exact resolve eq28 eq23837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23837
  have eq24029 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq23983
       have r₂ := eq23985
       grind)
    | exact resolve eq23983 eq23985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23983 eq23985
  have eq24056 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24029 eq98
    | exact resolve eq98 eq24029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq24029
  have eq24094 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24056
       have i₂ := eq7426
       grind)
    | exact superpose eq7426 eq24056
    | exact resolve eq24056 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7426 eq24056
  have eq24100 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq24094
    | exact resolve eq24094 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq24094
  have eq24195 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24100 eq7568
    | (have j0 := eq7568 (M.op (M.op x y) y)
       grind)
    | exact resolve eq7568 eq24100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7568
  have eq24211 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7438 eq24195
    | exact resolve eq24195 eq7438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24195
  have eq24212 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq24211
  have eq24306 : (M.op x y) ≠ (M.op x y) ∨ (k (k y (M.op x y)) (M.op x y)) = (M.op (k y (M.op x y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24212 eq8918
    | (have r₁ := eq8918
       have r₂ := eq24212
       grind)
    | exact resolve eq8918 eq24212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8918
  have eq24335 : (k (k y (M.op x y)) (M.op x y)) = (M.op (k y (M.op x y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq24306
  have eq24339 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23721 eq24335
    | exact resolve eq24335 eq23721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23721 eq24335
  have eq24341 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24100 eq24339
    | exact resolve eq24339 eq24100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24100 eq24339
  have eq24343 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24212 eq24341
    | exact resolve eq24341 eq24212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24212 eq24341
  have eq24344 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq24343
  have eq24444 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24344 eq20567
    | exact resolve eq20567 eq24344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20567
  have eq24457 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq24344
  have eq24470 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24444
  have eq24554 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24470 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq24470
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq24470
       grind)
    | exact resolve eq13 eq24470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24470
  have eq24572 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24554
  have eq24598 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20211 eq24572
    | exact resolve eq24572 eq20211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20211 eq24572
  have eq24609 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq24598
       have r₂ := eq24457
       grind)
    | exact resolve eq24598 eq24457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24457 eq24598
  have eq24613 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24609 eq27
    | exact resolve eq27 eq24609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24609
  have eq24849 : y = (M.op x y) := by
    first
    | (have r₁ := eq24613
       have r₂ := eq7470
       grind)
    | exact resolve eq24613 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24613
  have eq24892 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq24849
       grind)
    | exact superpose eq24849 eq24
    | exact resolve eq24 eq24849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq24950 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7438
       have i₂ := eq24849
       grind)
    | exact superpose eq24849 eq7438
    | exact resolve eq7438 eq24849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7438 eq24849
  have eq25040 : (σ x) = (σ y) := by
    first
    | exact superpose eq7439 eq24892
    | exact resolve eq24892 eq7439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7439 eq24892
  have eq25070 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25040 eq26
    | exact resolve eq26 eq25040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq25040
  have eq25328 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq24950 eq8648
    | exact resolve eq8648 eq24950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8648 eq24950
  have eq25364 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq25328
    | exact resolve eq25328 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq25328
  have eq25368 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq7470 eq25364
    | exact resolve eq25364 eq7470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25364
  have eq25428 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25070 eq28
    | exact resolve eq28 eq25070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25070
  have eq25455 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25368 eq25428
    | exact resolve eq25428 eq25368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25368 eq25428
  have eq25456 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25455
  have eq26088 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq25456 eq27
    | exact resolve eq27 eq25456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25456
  have eq26271 : False := by grind
  exact eq26271

/-- `Equation4612`: `(x ◇ x) ◇ y = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyx_pxx_pxy_Equation4612 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4612 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4612.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 x X0 X3
       have i₂ := eq9 x X0 X1
       grind)
    | (have i₁ := eq9 x x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 X3) X0
       have i₂ := eq9 X3 X0 X1
       grind)
    | (have i₁ := eq9 X0 (M.op X1 X2) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq9 X2 X1 x
       grind)
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq9 X1 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) X0) = (M.op (M.op (M.op X2 X2) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 (M.op X2 X2) X3 X0
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq63 (M.op X1 X2) X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X0 X3)) = (M.op (M.op (M.op X0 X1) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X0 X3) X3
       have i₂ := eq63 X0 X3 X1
       grind)
    | (have i₁ := eq9 X2 (M.op X0 X3) X3
       have i₂ := eq63 X0 X1 X3
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq199 : ∀ X0 X1 X4 X5 : G, (M.op (M.op (M.op X0 X1) X1) X0) = (M.op (M.op (M.op X4 X5) X5) X4) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq65 X4 X5 x x
       have i₂ := eq65 X0 X1 x x
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 X3) X3
       have i₂ := eq65 X3 X3 X0 X1
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1677 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq1726 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1677 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq1727 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1726 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq4457 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1727 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq4462 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4457 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq4457 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq4457 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq4457 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq4457 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4457
  have eq4512 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq4541 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 X1) X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq4462 X0 X2
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq4462 (M.op X1 X2) X1
       grind)
    | exact superpose eq4462 eq9
    | (have j1 := eq4462 X0 X2
       grind)
    | exact resolve eq9 eq4462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4661 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4512 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4662 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4512 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4512
  have eq4767 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4661 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4806 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4767 (σ X0)
       grind)
    | exact superpose eq4767 eq15
    | exact resolve eq15 eq4767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4817 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4806 X0
       have i₂ := eq4767 X0
       grind)
    | exact superpose eq4767 eq4806
    | exact resolve eq4806 eq4767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4767 eq4806
  have eq4989 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq4817 X0
       grind)
    | exact superpose eq4817 eq9
    | exact resolve eq9 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4993 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5000 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X1 X2 (σ X0)
       have i₂ := eq4817 X0
       grind)
    | exact superpose eq4817 eq68
    | exact resolve eq68 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5022 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4462 X1 (σ X0)
       have i₂ := eq4817 X0
       grind)
    | exact superpose eq4817 eq4462
    | (have j0 := eq4462 X1 (σ X0)
       grind)
    | exact resolve eq4462 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5035 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ (M.op X0 X0))) = (M.op (M.op (M.op (σ X0) X2) X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 (σ X0) X2 X1 (σ X0)
       have i₂ := eq4817 X0
       grind)
    | exact superpose eq4817 eq93
    | exact resolve eq93 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq4817
  have eq5052 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4993 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq4993
    | exact resolve eq4993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4993
  have eq5054 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5052
  have eq5995 : ∀ X0 X1 X3 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X3 X3)) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq4989 X3 X1 x
       have i₂ := eq4989 X0 X1 x
       grind)
    | exact superpose eq4989 eq4989
    | exact resolve eq4989 eq4989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4989
  have eq17256 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ (M.op (M.op X3 X3) (M.op X2 X2)) ∨ (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op X3 X3) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4662 (M.op X3 X3) (M.op X2 X2)
       have i₂ := eq255 X0 X1 X2 X3
       grind)
    | (have i₁ := eq4662 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq255 X0 X1 X2 X3
       grind)
    | exact superpose eq255 eq4662
    | (have r₁ := eq4662 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq255 X0 X1 X1 X0
       grind)
    | (have r₁ := eq4662 (M.op X2 X2) (M.op X3 X3)
       have r₂ := eq255 X3 X2 X2 X3
       grind)
    | exact resolve eq4662 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4662
  have eq17264 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op X3 X3) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq17256 X0 X1 X2 X3
       grind)
    | (have r₁ := eq17256 X2 X3 X1 X0
       have r₂ := eq255 X0 X1 X2 X3
       grind)
    | (have r₁ := eq17256 X0 X1 X3 X2
       have r₂ := eq255 X0 X1 X2 X3
       grind)
    | exact resolve eq17256 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq17256
  have eq35024 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq5022 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq5022 X0 (σ X0)
       grind)
    | exact superpose eq5022 eq10
    | (have j1 := eq5022 X1 X0
       grind)
    | exact resolve eq10 eq5022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5022
  have eq36718 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq35024 (σ X0) X1
       grind)
    | exact superpose eq35024 eq15
    | (have j1 := eq35024 (σ X0) X1
       grind)
    | exact resolve eq15 eq35024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35024
  have eq36743 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36718 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36718
    | (have j0 := eq36718 X0 X1
       grind)
    | exact resolve eq36718 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36718
  have eq41460 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36743 x y
       grind)
    | exact superpose eq36743 eq16
    | (have j1 := eq36743 x y
       grind)
    | exact resolve eq16 eq36743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41982 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41460
       have i₂ := eq4462 x y
       grind)
    | exact superpose eq4462 eq41460
    | (have j1 := eq4462 x y
       grind)
    | exact resolve eq41460 eq4462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41460
  have eq41986 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq41982
  have eq41987 : x = (M.op y y) := by grind
  clear eq41986
  have eq41992 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X0 X1
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq9
    | exact resolve eq9 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42000 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1 y
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq68
    | exact resolve eq68 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq42048 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5000 y X0 X1
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq5000
    | exact resolve eq5000 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5000
  have eq42051 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq5054 y
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq5054
    | exact resolve eq5054 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5054
  have eq42059 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5995 X0 X1 y
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq5995
    | exact resolve eq5995 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5995
  have eq42079 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op X2 X2) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17264 X0 X1 y X2
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq17264
    | exact resolve eq17264 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17264
  have eq42091 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq65 y y X0 X1
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq65
    | exact resolve eq65 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq42093 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq80 y y X0 X1
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq80
    | exact resolve eq80 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq42101 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1 y y
       have i₂ := eq41987
       grind)
    | exact superpose eq41987 eq199
    | exact resolve eq199 eq41987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq41987
  have eq43643 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ (M.op X0 X0))) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq5035 X0 X1 x
       have i₂ := eq42101 (σ X0) x
       grind)
    | exact superpose eq42101 eq5035
    | exact resolve eq5035 eq42101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035 eq42101
  have eq46744 : ∀ X2 : G, (k (M.op X2 X2) x) = (M.op (M.op x y) y) := by
    intro X2
    first
    | (have i₁ := eq42079 x x X2
       have i₂ := eq42091 x x
       grind)
    | exact superpose eq42091 eq42079
    | exact resolve eq42079 eq42091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42079 eq42091
  have eq51075 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (σ x) X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq4541 X0 x X2
       have i₂ := eq42048 x X2
       grind)
    | exact superpose eq42048 eq4541
    | (have j0 := eq4541 X0 x X2
       grind)
    | exact resolve eq4541 eq42048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4541
  have eq52771 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (σ x) X1) X1) := by
    intro X1
    first
    | (have i₁ := eq42093 x X1
       have i₂ := eq42048 x X1
       grind)
    | exact superpose eq42048 eq42093
    | exact resolve eq42093 eq42048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42093
  have eq54692 : ∀ X1 : G, (M.op x X1) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq42048 x X1
       have i₂ := eq42000 x X1
       grind)
    | exact superpose eq42000 eq42048
    | exact resolve eq42048 eq42000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42048
  have eq54700 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ (M.op X0 X0))) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq43643 X0 X1
       have i₂ := eq41992 x y
       grind)
    | exact superpose eq41992 eq43643
    | exact resolve eq43643 eq41992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43643
  have eq59209 : ∀ X2 : G, (M.op x x) = (k (M.op X2 X2) x) := by
    intro X2
    first
    | (have i₁ := eq46744 X2
       have i₂ := eq41992 x y
       grind)
    | exact superpose eq41992 eq46744
    | exact resolve eq46744 eq41992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46744
  have eq63938 : (M.op (M.op x y) y) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq52771 x
       have i₂ := eq41992 (σ x) x
       grind)
    | exact superpose eq41992 eq52771
    | exact resolve eq52771 eq41992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52771
  have eq66405 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42059 X0 X1
       have i₂ := eq54692 X1
       grind)
    | exact superpose eq54692 eq42059
    | exact resolve eq42059 eq54692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42059
  have eq66410 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = (M.op x X2) := by
    intro X0 X2
    first
    | (have i₁ := eq51075 X0 X2
       have i₂ := eq54692 X2
       grind)
    | exact superpose eq54692 eq51075
    | (have j0 := eq51075 X0 X2
       grind)
    | exact resolve eq51075 eq54692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51075
  have eq66658 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54692 (σ y)
       grind)
    | exact superpose eq54692 eq16
    | exact resolve eq16 eq54692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66728 : ∀ X0 : G, (M.op x x) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq54700 X0 x
       have i₂ := eq42000 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq42000 eq54700
    | exact resolve eq54700 eq42000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42000 eq54700
  have eq75375 : (M.op x x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq63938
       have i₂ := eq41992 x y
       grind)
    | exact superpose eq41992 eq63938
    | exact resolve eq63938 eq41992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63938
  have eq111809 : ∀ X0 X1 : G, (M.op x x) = (k X0 x) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59209 X1
       have i₂ := eq4462 X0 X1
       grind)
    | (have i₁ := eq59209 x
       have i₂ := eq4462 (M.op x x) X1
       grind)
    | exact superpose eq4462 eq59209
    | (have j1 := eq4462 (k X0 x) x
       grind)
    | exact resolve eq59209 eq4462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4462 eq59209
  have eq112897 : (M.op x (σ y)) = (M.op (σ (M.op y x)) (σ x)) := by
    first
    | (have i₁ := eq41992 (σ y) (σ x)
       have i₂ := eq42051
       grind)
    | exact superpose eq42051 eq41992
    | exact resolve eq41992 eq42051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42051
  have eq121254 : (M.op x (σ y)) = (σ (k (M.op y x) x)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq36743 (M.op y x) x
       have i₂ := eq112897
       grind)
    | exact superpose eq112897 eq36743
    | (have j0 := eq36743 (M.op y x) x
       grind)
    | exact resolve eq36743 eq112897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36743
  have eq121263 : (M.op x (σ y)) ≠ (M.op (σ x) (σ (M.op y x))) ∨ (M.op x (σ y)) = (k (σ (M.op y x)) (σ x)) := by
    first
    | (have i₁ := eq4661 (σ (M.op y x)) (σ x)
       have i₂ := eq112897
       grind)
    | exact superpose eq112897 eq4661
    | exact resolve eq4661 eq112897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4661
  have eq121272 : (M.op x (σ y)) ≠ (M.op x (σ (M.op y x))) ∨ (M.op x (σ y)) = (k (σ (M.op y x)) (σ x)) := by
    first
    | (have i₁ := eq121263
       have i₂ := eq54692 (σ (M.op y x))
       grind)
    | exact superpose eq54692 eq121263
    | exact resolve eq121263 eq54692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54692 eq121263
  have eq121283 : (M.op x (σ y)) = (σ (k (M.op y x) x)) ∨ (M.op x (σ y)) ≠ (M.op x (σ (M.op y x))) := by
    first
    | (have i₁ := eq121272
       have i₂ := eq15 (M.op y x) x
       grind)
    | exact superpose eq15 eq121272
    | exact resolve eq121272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121272
  have eq149220 : ∀ X0 : G, (M.op x x) ≠ (M.op X0 x) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq111809 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111809
  have eq149224 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq149220 X0
       have j1 := eq66410 X0 x
       grind)
    | (have r₁ := eq149220 x
       have r₂ := eq66410 x x
       grind)
    | (have r₁ := eq149220 X0
       have r₂ := eq66410 X0 x
       grind)
    | exact resolve eq149220 eq66410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66410 eq149220
  have eq149281 : (M.op x (σ y)) = (σ (M.op (M.op y x) x)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq121254
       have i₂ := eq149224 (M.op y x)
       grind)
    | exact superpose eq149224 eq121254
    | exact resolve eq121254 eq149224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121254
  have eq149283 : (M.op x (σ y)) = (σ (M.op (M.op y x) x)) ∨ (M.op x (σ y)) ≠ (M.op x (σ (M.op y x))) := by
    first
    | (have i₁ := eq121283
       have i₂ := eq149224 (M.op y x)
       grind)
    | exact superpose eq149224 eq121283
    | exact resolve eq121283 eq149224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121283 eq149224
  have eq149428 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (M.op x (σ y)) ≠ (M.op x (σ (M.op y x))) := by
    first
    | (have i₁ := eq149283
       have i₂ := eq41992 y x
       grind)
    | exact superpose eq41992 eq149283
    | exact resolve eq149283 eq41992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149283
  have eq149430 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq149281
       have i₂ := eq41992 y x
       grind)
    | exact superpose eq41992 eq149281
    | exact resolve eq149281 eq41992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41992 eq149281
  have eq149448 : (M.op x (σ y)) ≠ (M.op x (σ (M.op y x))) := by
    first
    | (have r₁ := eq149428
       have r₂ := eq66658
       grind)
    | exact resolve eq149428 eq66658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149428
  have eq149450 : (M.op x x) = (M.op y x) := by
    first
    | (have r₁ := eq149430
       have r₂ := eq66658
       grind)
    | exact resolve eq149430 eq66658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66658 eq149430
  have eq149456 : (M.op x (σ y)) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq112897
       have i₂ := eq149450
       grind)
    | exact superpose eq149450 eq112897
    | exact resolve eq112897 eq149450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112897
  have eq149480 : (M.op x (σ y)) ≠ (M.op x (σ (M.op x x))) := by
    first
    | (have i₁ := eq149448
       have i₂ := eq149450
       grind)
    | exact superpose eq149450 eq149448
    | exact resolve eq149448 eq149450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149448 eq149450
  have eq149482 : (M.op x x) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq149480
       have i₂ := eq66728 x
       grind)
    | exact superpose eq66728 eq149480
    | exact resolve eq149480 eq66728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66728 eq149480
  have eq149504 : (M.op x (σ x)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq149456
       have i₂ := eq66405 x (σ x)
       grind)
    | exact superpose eq66405 eq149456
    | exact resolve eq149456 eq66405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66405 eq149456
  have eq149524 : (M.op x x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq149504
       have i₂ := eq75375
       grind)
    | exact superpose eq75375 eq149504
    | exact resolve eq149504 eq75375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75375 eq149504
  have eq149586 : False := by grind
  exact eq149586

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_pxx_pxy_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq57 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 (M.op X0 X1)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X1 X2
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X1 (M.op X0 X1)
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X1
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X1
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq110 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq118 : ∀ X0 X1 : G, (τ (σ X1)) = (k X1 (τ (M.op X0 (σ X1)))) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (M.op X0 (σ X1)) X1
       have i₂ := eq112 X0 (σ X1)
       grind)
    | exact superpose eq112 eq29
    | (have j1 := eq112 X0 (σ X1)
       grind)
    | exact resolve eq29 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq121 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 (σ X1)))) = X1 ∨ (M.op X0 (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq118 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq118
    | (have j0 := eq118 X0 X1
       grind)
    | exact resolve eq118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq394 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq57 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq57
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq412 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq405 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq405
    | (have j0 := eq405 (σ X0) (σ X1)
       grind)
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq405 X0 (τ X1)
       grind)
    | exact superpose eq405 eq19
    | (have j1 := eq405 X0 (τ X1)
       grind)
    | exact resolve eq19 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq431 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq405 (σ X0) X1
       grind)
    | exact superpose eq405 eq29
    | (have j1 := eq405 (σ X0) X1
       grind)
    | exact resolve eq29 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq525 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq424
    | exact resolve eq424 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq566 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq525
    | (have j0 := eq525 X0 X1
       grind)
    | exact resolve eq525 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq1004 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    grind
  have eq1092 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1004 X1 (M.op X0 X1)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq1004
    | exact resolve eq1004 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1240 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X1) (σ X0)
       have i₂ := eq412 X0 X1
       grind)
    | exact superpose eq412 eq57
    | (have j1 := eq412 X0 (k X0 X1)
       grind)
    | exact resolve eq57 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1261 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) (σ X1)
       have i₂ := eq412 X0 X1
       grind)
    | exact superpose eq412 eq57
    | (have j1 := eq412 X0 X1
       grind)
    | exact resolve eq57 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq1729 : ∀ X0 X1 : G, (M.op X0 (σ (k (τ X0) X1))) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1240 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1240
    | exact resolve eq1240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1739 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq1740 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1240 X1 (M.op X0 X1)
       have i₂ := eq1092 X0 X1
       grind)
    | exact superpose eq1092 eq1240
    | (have j0 := eq1240 X1 (M.op X0 X1)
       have j1 := eq1092 X0 X1
       grind)
    | exact resolve eq1240 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1791 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1740 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1792 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1739 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq1805 : ∀ X0 X1 : G, (M.op X0 (k X0 (σ X1))) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1729 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1729
    | (have j0 := eq1729 X0 X1
       grind)
    | exact resolve eq1729 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq1831 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) (σ (M.op X0 X0)) x
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq60
    | exact resolve eq60 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1835 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq110
    | exact resolve eq110 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq1792
  have eq1855 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1835 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq1835
    | (have j0 := eq1835 X0
       grind)
    | exact resolve eq1835 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1864 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq1855
  have eq2155 : ∀ X0 X1 : G, (M.op X1 (k X1 X0)) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1805 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1805
    | exact resolve eq1805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq2212 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2155 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq2155
    | (have j0 := eq2155 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq2155 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2230 : ∀ X0 X1 : G, (k X1 X0) = (M.op (k X1 X0) X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 (k X1 X0)
       have i₂ := eq2155 X0 X1
       grind)
    | exact superpose eq2155 eq57
    | (have j1 := eq2155 X1 (k X1 X0)
       grind)
    | exact resolve eq57 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq2256 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq2212 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212
  have eq5094 : ∀ X0 : G, (k X0 (τ (σ X0))) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq431 X0 (σ X0)
       have i₂ := eq1864 X0
       grind)
    | exact superpose eq1864 eq431
    | (have j1 := eq1864 X0
       grind)
    | exact resolve eq431 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq1864
  have eq5154 : ∀ X0 : G, (k X0 (τ (σ X0))) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5094
  have eq5174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ (σ X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5154 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5154
    | (have j0 := eq5154 X0
       grind)
    | exact resolve eq5154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154
  have eq5184 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5174 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5174
    | (have j0 := eq5174 X0
       grind)
    | exact resolve eq5174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5174
  have eq5227 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (M.op X0 X0)
       have i₂ := eq5184 X0
       grind)
    | exact superpose eq5184 eq24
    | (have j1 := eq5184 X0
       grind)
    | exact resolve eq24 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5184
  have eq5282 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5227 X0 X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq5227
    | (have j0 := eq5227 X0 X1
       grind)
    | exact resolve eq5227 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5227
  have eq12566 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1261 y x
       grind)
    | exact superpose eq1261 eq16
    | (have j1 := eq1261 y x
       grind)
    | exact resolve eq16 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12635 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X1) (σ X0)
       have i₂ := eq1261 X0 X1
       grind)
    | exact superpose eq1261 eq57
    | (have j1 := eq1261 (k X0 X1) X0
       grind)
    | exact resolve eq57 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14318 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12566
       have i₂ := eq566 x y
       grind)
    | exact superpose eq566 eq12566
    | (have j1 := eq566 (σ y) (σ x)
       grind)
    | (have r₁ := eq12566
       have r₂ := eq566 x y
       grind)
    | exact resolve eq12566 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq12566
  have eq14319 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq14318
  have eq14332 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq57 (σ x) (σ y)
       have i₂ := eq14319
       grind)
    | exact superpose eq14319 eq57
    | exact resolve eq57 eq14319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14538 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121 (σ x) y
       have i₂ := eq14319
       grind)
    | exact superpose eq14319 eq121
    | exact resolve eq121 eq14319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14319
  have eq14539 : x = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121 (σ y) x
       have i₂ := eq14332
       grind)
    | exact superpose eq14332 eq121
    | exact resolve eq121 eq14332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq14332
  have eq14593 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14539
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14539
    | exact resolve eq14539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14539
  have eq14594 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14538
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14538
    | exact resolve eq14538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14538
  have eq20401 : ∀ X0 X1 : G, (M.op X0 (σ (k (τ X0) X1))) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12635 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12635
    | exact resolve eq12635 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20537 : ∀ X0 X1 : G, (M.op X0 (k X0 (σ X1))) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20401 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq20401
    | (have j0 := eq20401 X0 X1
       grind)
    | exact resolve eq20401 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20401
  have eq20810 : ∀ X0 X1 : G, (M.op X1 (k X1 X0)) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20537 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20537
    | exact resolve eq20537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20537
  have eq20941 : ∀ X0 X1 : G, (k X1 X0) = (M.op (k X1 X0) X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 (k X1 X0)
       have i₂ := eq20810 X0 X1
       grind)
    | exact superpose eq20810 eq57
    | (have j1 := eq20810 (k X1 X0) X1
       grind)
    | exact resolve eq57 eq20810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20944 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (k X1 X0) (M.op X2 X2))) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X1 (k X1 X0) X2
       have i₂ := eq20810 X0 X1
       grind)
    | exact superpose eq20810 eq60
    | (have j1 := eq20810 X1 (M.op (k X1 X0) (M.op X2 X2))
       grind)
    | exact resolve eq60 eq20810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq20810
  have eq25904 : y = (M.op y (τ (σ x))) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2256 y
       have i₂ := eq14594
       grind)
    | exact superpose eq14594 eq2256
    | exact resolve eq2256 eq14594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256 eq14594
  have eq26076 : y = (M.op y x) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq25904
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25904
    | exact resolve eq25904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25904
  have eq26077 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq26076
  have eq26098 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq405 y x
       have i₂ := eq26077
       grind)
    | exact superpose eq26077 eq405
    | (have j0 := eq405 y x
       grind)
    | exact resolve eq405 eq26077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq26113 : y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2230 x y
       have i₂ := eq26077
       grind)
    | exact superpose eq26077 eq2230
    | (have j0 := eq2230 y y
       grind)
    | exact resolve eq2230 eq26077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230 eq26077
  have eq26145 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq26113
  have eq26158 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq26098
  have eq26388 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57 y x
       have i₂ := eq26158
       grind)
    | exact superpose eq26158 eq57
    | exact resolve eq57 eq26158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26158
  have eq106829 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq5282
  have eq106887 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq106829 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106829
  have eq106898 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq106887 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq106887
    | exact resolve eq106887 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq106887
  have eq106928 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq106898 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq106898
    | exact resolve eq106898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106898
  have eq107350 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq106928 X0
       have i₂ := eq24 (σ X0) X0
       grind)
    | exact superpose eq24 eq106928
    | exact resolve eq106928 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq106928
  have eq107394 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq107350 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq107350
    | exact resolve eq107350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107350
  have eq107675 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq107394 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq107394
    | exact resolve eq107394 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107966 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq107675 X0
       have i₂ := eq107394 X0
       grind)
    | exact superpose eq107394 eq107675
    | exact resolve eq107675 eq107394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107394 eq107675
  have eq108519 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (M.op (σ (M.op X1 X1)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1831 X1 (σ X0)
       have i₂ := eq107966 X0
       grind)
    | exact superpose eq107966 eq1831
    | exact resolve eq1831 eq107966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq158638 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op y x) := by grind
  clear eq14593
  have eq158650 : (σ y) = (σ (k x y)) ∨ x = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq158638
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq158638
    | exact resolve eq158638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158638
  have eq158669 : (k x y) = (τ (σ y)) ∨ x = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq158650
       grind)
    | exact superpose eq158650 eq10
    | exact resolve eq10 eq158650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158650
  have eq158801 : y = (k x y) ∨ x = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq158669
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq158669
    | exact resolve eq158669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158669
  have eq158849 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq20941 y x
       have i₂ := eq158801
       grind)
    | exact superpose eq158801 eq20941
    | (have j0 := eq20941 y x
       grind)
    | exact resolve eq20941 eq158801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20941 eq158801
  have eq158867 : x = (k x y) ∨ y = (M.op y x) := by grind
  clear eq158849
  have eq158939 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 X0))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq20944 y x X0
       have i₂ := eq158867
       grind)
    | exact superpose eq158867 eq20944
    | (have j0 := eq20944 x (M.op x (M.op X0 X0)) x
       grind)
    | exact resolve eq20944 eq158867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20944 eq158867
  have eq158956 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 X0))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq158939 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158939
  have eq164429 : x = (M.op x (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq158956 y
       have i₂ := eq26145
       grind)
    | exact superpose eq26145 eq158956
    | exact resolve eq158956 eq26145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26145 eq158956
  have eq164556 : x = (M.op x (M.op x y)) ∨ y = (M.op y x) := by grind
  clear eq164429
  have eq166574 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq164556
       have i₂ := eq26388
       grind)
    | exact superpose eq26388 eq164556
    | exact resolve eq164556 eq26388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26388 eq164556
  have eq166690 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq166574
  have eq166699 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57 y x
       have i₂ := eq166690
       grind)
    | exact superpose eq166690 eq57
    | exact resolve eq57 eq166690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166690
  have eq166797 : x = (M.op x y) := by grind
  clear eq166699
  have eq166836 : y = (M.op y x) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq166797
       grind)
    | exact superpose eq166797 eq57
    | exact resolve eq57 eq166797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166861 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1791 x y
       have i₂ := eq166797
       grind)
    | exact superpose eq166797 eq1791
    | exact resolve eq1791 eq166797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166945 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1791 y x
       have i₂ := eq166836
       grind)
    | exact superpose eq166836 eq1791
    | exact resolve eq1791 eq166836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791 eq166836
  have eq173714 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq57 (σ y) (σ x)
       have i₂ := eq166861
       grind)
    | exact superpose eq166861 eq57
    | exact resolve eq57 eq166861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166861
  have eq175756 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq166945
       grind)
    | exact superpose eq166945 eq16
    | exact resolve eq16 eq166945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166945
  have eq175892 : (σ x) ≠ (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq175756
       have i₂ := eq166797
       grind)
    | exact superpose eq166797 eq175756
    | exact resolve eq175756 eq166797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175756
  have eq175893 : x = (k x y) := by grind
  clear eq175892
  have eq175924 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1240 x y
       have i₂ := eq175893
       grind)
    | exact superpose eq175893 eq1240
    | (have j0 := eq1240 x x
       grind)
    | exact resolve eq1240 eq175893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq175969 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq175924
       have i₂ := eq107966 x
       grind)
    | exact superpose eq107966 eq175924
    | exact resolve eq175924 eq107966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175924
  have eq176315 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq173714
       grind)
    | exact superpose eq173714 eq16
    | exact resolve eq16 eq173714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173714
  have eq176452 : (σ x) ≠ (σ x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq176315
       have i₂ := eq166797
       grind)
    | exact superpose eq166797 eq176315
    | exact resolve eq176315 eq166797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176315
  have eq176453 : y = (k y x) := by grind
  clear eq176452
  have eq176829 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12635 y x
       have i₂ := eq176453
       grind)
    | exact superpose eq176453 eq12635
    | (have j0 := eq12635 y y
       grind)
    | exact resolve eq12635 eq176453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12635 eq176453
  have eq176863 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq176829
       have i₂ := eq107966 y
       grind)
    | exact superpose eq107966 eq176829
    | exact resolve eq176829 eq107966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107966 eq176829
  have eq201424 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175969
       grind)
    | exact superpose eq175969 eq16
    | exact resolve eq16 eq175969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175969
  have eq201575 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq201424
       have i₂ := eq166797
       grind)
    | exact superpose eq166797 eq201424
    | exact resolve eq201424 eq166797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201424
  have eq201576 : (σ x) = (σ (M.op x x)) := by grind
  clear eq201575
  have eq201607 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq108519 x X0
       have i₂ := eq201576
       grind)
    | exact superpose eq201576 eq108519
    | exact resolve eq108519 eq201576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108519 eq201576
  have eq642244 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq176863
       grind)
    | exact superpose eq176863 eq16
    | exact resolve eq16 eq176863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176863
  have eq642621 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq642244
       have i₂ := eq166797
       grind)
    | exact superpose eq166797 eq642244
    | exact resolve eq642244 eq166797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642244
  have eq642622 : (σ y) = (σ (M.op y y)) := by grind
  clear eq642621
  have eq642742 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq201607 y
       have i₂ := eq642622
       grind)
    | exact superpose eq642622 eq201607
    | exact resolve eq201607 eq642622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201607 eq642622
  have eq685869 : (σ y) = (M.op (σ y) (σ (k x y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq642742
       have i₂ := eq1261 x y
       grind)
    | exact superpose eq1261 eq642742
    | (have j1 := eq1261 (k x y) y
       grind)
    | exact resolve eq642742 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261 eq642742
  have eq686162 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq685869
       have i₂ := eq175893
       grind)
    | exact superpose eq175893 eq685869
    | exact resolve eq685869 eq175893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175893 eq685869
  have eq686163 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq686162
  have eq686201 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57 (σ y) (σ x)
       have i₂ := eq686163
       grind)
    | exact superpose eq686163 eq57
    | exact resolve eq57 eq686163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq686163
  have eq686520 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq686201
       grind)
    | exact superpose eq686201 eq16
    | exact resolve eq16 eq686201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686201
  have eq686850 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq686520
       have i₂ := eq166797
       grind)
    | exact superpose eq166797 eq686520
    | exact resolve eq686520 eq166797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166797 eq686520
  have eq686851 : False := by grind
  exact eq686851

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_y_pxy_Equation840 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
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
  clear eq47
  have eq131 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq177 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) X0 X2
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq182 eq177
    | exact resolve eq177 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : y ≠ y ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq182 eq13
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq182
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq193 : y = (k (M.op x y) y) := by grind
  clear eq191
  have eq194 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq183 eq177
    | exact resolve eq177 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ y) ≠ (σ y) ∨ (σ y) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq183 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq183
       grind)
    | exact resolve eq13 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq197 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq195
  have eq199 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq190 eq13
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq190
       grind)
    | exact resolve eq13 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : (M.op x y) = (k y (M.op x y)) := by grind
  clear eq199
  have eq202 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq193 eq37
    | exact resolve eq37 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq193
  have eq205 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq202
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq202
    | exact resolve eq202 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq202
  have eq208 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq194 eq13
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq194
       grind)
    | exact resolve eq13 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq208
  have eq211 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq201 eq36
    | exact resolve eq36 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq201
  have eq214 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq211
    | exact resolve eq211 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq296 : (τ (M.op (σ x) (σ y))) = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq210 eq107
    | exact resolve eq107 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq210
  have eq372 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq373 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq177
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1447 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq372
       grind)
    | exact superpose eq372 eq40
    | exact resolve eq40 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq372
  have eq1448 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1447
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1447
    | exact resolve eq1447 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq1450 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq1448
    | exact resolve eq1448 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1450 eq373
    | exact resolve eq373 eq1450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1672 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1665
       have r₂ := eq27
       grind)
    | exact resolve eq1665 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq1683 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1672 eq177
    | exact resolve eq177 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1692 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq1683
    | exact resolve eq1683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq1693 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1692
  have eq1805 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq1693
       grind)
    | exact superpose eq1693 eq177
    | exact resolve eq177 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq1815 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1805
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1805
    | exact resolve eq1805 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq1816 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1815
  have eq1825 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1816 eq197
    | exact resolve eq197 eq1816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq1829 : (τ (σ x)) = (k y (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1816 eq296
    | exact resolve eq296 eq1816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq1816
  have eq1837 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1829
    | exact resolve eq1829 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1829
  have eq1919 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1825 eq1450
    | exact resolve eq1450 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450 eq1825
  have eq1925 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1919
  have eq1979 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq1925
       grind)
    | exact superpose eq1925 eq177
    | exact resolve eq177 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq1989 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1979
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1979
    | exact resolve eq1979 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq1990 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1989
  have eq1993 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1990 eq28
    | exact resolve eq28 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1999 : (k (M.op x y) x) = (τ (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1990 eq131
    | exact resolve eq131 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq1990
  have eq2021 : (k y x) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114 eq1999
    | exact resolve eq1999 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1999
  have eq2027 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1993
    | exact resolve eq1993 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1993
  have eq2029 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1837 eq2021
    | exact resolve eq2021 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837 eq2021
  have eq2035 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2027
       grind)
    | exact superpose eq2027 eq18
    | exact resolve eq18 eq2027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2041 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq190
       have i₂ := eq2027
       grind)
    | exact superpose eq2027 eq190
    | exact resolve eq190 eq2027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq2027
  have eq2161 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2041 eq187
    | exact resolve eq187 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq2041
  have eq4344 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2035 eq2161
    | exact resolve eq2161 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq4433 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4344 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4344
  have eq43221 : x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2029 eq382
    | (have j0 := eq382 x x
       grind)
    | exact resolve eq382 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029
  have eq43350 : x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2035 eq43221
    | exact resolve eq43221 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43221
  have eq43351 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq43350
  have eq43489 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43351 eq177
    | exact resolve eq177 eq43351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43351
  have eq43694 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2035 eq43489
    | exact resolve eq43489 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43489
  have eq43695 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq43694
  have eq43722 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4433 x
       have i₂ := eq43695
       grind)
    | exact superpose eq43695 eq4433
    | exact resolve eq4433 eq43695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4433 eq43695
  have eq44175 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq43722
  have eq44232 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2035 eq44175
    | exact resolve eq44175 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035 eq44175
  have eq44233 : x = (M.op x y) := by grind
  clear eq44232
  have eq44243 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq44233
       grind)
    | exact superpose eq44233 eq22
    | exact resolve eq22 eq44233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq44233
  have eq44261 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq44243 eq20
    | exact resolve eq20 eq44243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq44243
  have eq44380 : (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq44261 eq205
    | exact resolve eq205 eq44261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq44381 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq44261 eq214
    | exact resolve eq214 eq44261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq44441 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44380 eq373
    | exact resolve eq373 eq44380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq44380
  have eq44461 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44381 eq382
    | (have j0 := eq382 (σ x) (σ x)
       grind)
    | exact resolve eq382 eq44381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq44381
  have eq44466 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq44461
    | exact resolve eq44461 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44461
  have eq47539 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44441 eq177
    | exact resolve eq177 eq44441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44441
  have eq47617 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq47539
    | exact resolve eq47539 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47539
  have eq47618 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq47617
  have eq47628 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47618 eq194
    | exact resolve eq194 eq47618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq47668 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq47628 eq16
    | exact resolve eq16 eq47628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47628
  have eq59619 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44466 eq177
    | exact resolve eq177 eq44466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq44466
  have eq59711 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq59619
    | exact resolve eq59619 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59619
  have eq59712 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq59711
  have eq59987 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59712 eq47668
    | exact resolve eq47668 eq59712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47668 eq59712
  have eq59994 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq59987
  have eq60007 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq59994
    | exact resolve eq59994 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59994
  have eq60031 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47618 eq60007
    | exact resolve eq60007 eq47618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47618 eq60007
  have eq60036 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq60031
    | exact resolve eq60031 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq60031
  have eq60037 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60036
  have eq60040 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq60037 eq27
    | exact resolve eq27 eq60037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq60037
  have eq60064 : False := by grind
  exact eq60064

/-- `Equation934`: `x = y ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_y_pyx_x_pyx_Equation934 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law934 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law934.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X2) (M.op X2 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op y X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 (M.op (M.op X1 X2) (M.op X2 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X3 X0)) = (M.op X1 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X3) (M.op X3 X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq44
    | exact resolve eq44 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq75 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq80 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq105 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq80 sF3 (σ X0)
       grind)
    | exact superpose eq80 eq37
    | (have j1 := eq80 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq69 sF3
       grind)
    | exact superpose eq69 eq104
    | exact resolve eq104 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq69 y
       grind)
    | exact superpose eq69 eq108
    | exact resolve eq108 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq80 y x
       grind)
    | exact superpose eq80 eq103
    | (have j1 := eq80 y x
       grind)
    | exact resolve eq103 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
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
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq118
    | exact resolve eq118 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq139 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq158 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq155
       have i₂ := eq69 sF1
       grind)
    | exact superpose eq69 eq155
    | exact resolve eq155 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq160 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq158
       have i₂ := eq69 sF0
       grind)
    | exact superpose eq69 eq158
    | exact resolve eq158 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq158
  have eq181 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq160 eq16
    | exact resolve eq16 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X0)) = (M.op X1 (M.op (M.op X1 x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (M.op X1 X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op sF3 x) (M.op x X0))
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op X1 (M.op (M.op X1 (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 : G, (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X0 X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq80 (τ X1) X0
       grind)
    | exact superpose eq80 eq35
    | (have j1 := eq80 (τ X1) X0
       grind)
    | exact resolve eq35 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq580 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X1 (M.op (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X4) (M.op X4 X0)) = (M.op X1 (M.op X2 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X2 X1 X3 (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X4) (M.op X4 X0))
       have i₂ := eq14 X0 (M.op (M.op X1 X3) (M.op X3 X2)) X4
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 X0)) = (M.op X4 (M.op (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X5) (M.op X5 X4)) X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X2 X1 X3 (M.op X4 (M.op (M.op (M.op (M.op (M.op X1 X3) (M.op X3 X2)) X5) (M.op X5 X4)) X0))
       have i₂ := eq53 X4 (M.op (M.op X1 X3) (M.op X3 X2)) X5 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X2) X1 X2 (M.op (M.op X2 (M.op X1 X2)) X0)
       have i₂ := eq14 X0 (M.op X1 X2) (M.op X2 (M.op X1 X2))
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1)) = (M.op X2 (M.op (M.op X2 (σ x)) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op X2 (M.op (M.op X2 X0) (M.op (M.op X1 x) (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X1 X0) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq724 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq56 X2 X0 X1 x
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X4) X3) = (M.op X1 (M.op X4 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X1 X2 (M.op (M.op X2 X4) X3)
       have i₂ := eq56 X3 X0 (M.op X1 X2) (M.op X2 X4)
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 X2) (M.op (M.op (M.op X3 (M.op X1 X4)) (M.op X0 (M.op (M.op X0 X1) X2))) X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X4 X2) X3 (M.op X1 X4) X5
       have i₂ := eq56 X2 X0 X1 X4
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq750 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq723 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq723
    | (have j0 := eq723 y
       grind)
    | exact resolve eq723 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq776 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq724
    | (have j0 := eq724 (σ y)
       grind)
    | exact resolve eq724 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq119 eq80
    | (have j0 := eq80 (σ y) (σ x)
       grind)
    | exact resolve eq80 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq119
  have eq921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq920
    | exact resolve eq920 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq924 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq921
       have r₂ := eq28
       grind)
    | exact resolve eq921 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq926 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq924 eq139
    | exact resolve eq139 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq924
  have eq944 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq926
    | exact resolve eq926 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq945 : x = (M.op y y) := by grind
  clear eq944
  have eq946 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq110
    | exact resolve eq110 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq947 : y = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq51
    | exact resolve eq51 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 : G, (M.op y (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq14
    | exact resolve eq14 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 y
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq14
    | exact resolve eq14 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq946
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq946
    | exact resolve eq946 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq1068 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq964 eq52
    | exact resolve eq52 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq964 eq14
    | exact resolve eq14 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq964 eq14
    | exact resolve eq14 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1163 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq954 y
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq954
    | exact resolve eq954 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1185 : (M.op x x) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq954 (M.op x x)
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq954
    | exact resolve eq954 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq1163
  have eq1195 : (M.op x x) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1185
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1185
    | exact resolve eq1185 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1304 : (M.op x (M.op (M.op x y) y)) = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq51 (M.op (M.op y y) x)
       have i₂ := eq955 y
       grind)
    | exact superpose eq955 eq51
    | exact resolve eq51 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq955
  have eq1307 : (M.op x x) = (M.op x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq1304
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq1304
    | exact resolve eq1304 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1311 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq964 eq1075
    | exact resolve eq1075 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1335 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1311 eq1075
    | exact resolve eq1075 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1345 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq1335
    | exact resolve eq1335 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1494 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op X0 x) (M.op x x))) := by
    intro X0
    first
    | exact superpose eq1307 eq14
    | exact resolve eq14 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq1500 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1494 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq1494
    | exact resolve eq1494 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq1543 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq598
    | (have j0 := eq598 X0 (σ x) (σ y)
       grind)
    | exact resolve eq598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1562 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq947 eq598
    | exact resolve eq598 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1563 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq1068 eq598
    | exact resolve eq598 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1646 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq1345 eq1543
    | exact resolve eq1543 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1673 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) := by
    first
    | exact superpose eq1562 eq160
    | exact resolve eq160 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1730 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1195 eq1673
    | exact resolve eq1673 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq1749 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1730
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq1730
    | exact resolve eq1730 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1730
  have eq1893 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq721
    | (have j0 := eq721 X0 (σ x) (σ y)
       grind)
    | exact resolve eq721 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1942 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq721
    | exact resolve eq721 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1976 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq750 eq721
    | exact resolve eq721 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq1983 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq776 eq721
    | exact resolve eq721 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq2004 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1345 eq1983
    | exact resolve eq1983 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq2009 : (M.op x y) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq1195 eq1976
    | exact resolve eq1976 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq2025 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (M.op X1 X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq1563 eq1942
    | exact resolve eq1942 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942
  have eq2046 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1563 eq1893
    | exact resolve eq1893 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq2164 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (σ x) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq727
    | exact resolve eq727 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2186 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2004 eq727
    | exact resolve eq727 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2270 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ y) X0)) (M.op (σ x) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1563 eq2164
    | exact resolve eq2164 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164
  have eq2325 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq1749 eq2004
    | exact resolve eq2004 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq2327 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1749 eq1311
    | exact resolve eq1311 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq2387 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2325 eq727
    | exact resolve eq727 eq2325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2410 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) := by
    first
    | exact superpose eq2327 eq721
    | exact resolve eq721 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2659 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 x) X0)) = (M.op y (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq1562 eq248
    | exact resolve eq248 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq2661 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq2410 eq1076
    | exact resolve eq1076 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2819 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq1749 eq1646
    | exact resolve eq1646 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq3172 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq2186 eq2046
    | exact resolve eq2046 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046 eq2186
  have eq3208 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq964 eq3172
    | exact resolve eq3172 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3172
  have eq3289 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (M.op X1 X0)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq1563 eq250
    | exact resolve eq250 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq3602 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 (σ x)) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq1563 eq252
    | exact resolve eq252 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq3754 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (M.op (σ y) (M.op (σ y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1563 eq253
    | exact resolve eq253 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq3867 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2819 (M.op sF1 (M.op sF1 X0))
       have i₂ := eq721 X0 sF1 sF1
       grind)
    | exact superpose eq721 eq2819
    | exact resolve eq2819 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3887 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2819 eq727
    | exact resolve eq727 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3890 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2819 eq14
    | exact resolve eq14 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3928 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y))))) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2819 eq3754
    | exact resolve eq3754 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754
  have eq3949 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2327 eq3928
    | exact resolve eq3928 eq2327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327 eq3928
  have eq3990 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq964 eq3949
    | exact resolve eq3949 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3949
  have eq4751 : (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2819 eq260
    | exact resolve eq260 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4846 : (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq4751
    | exact resolve eq4751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4751
  have eq5097 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq261 eq52
    | exact resolve eq52 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq261
  have eq5102 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq263 eq5097
    | exact resolve eq5097 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5097
  have eq5151 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ y) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq1563 eq5102
    | exact resolve eq5102 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5102
  have eq5170 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq964 eq5151
    | exact resolve eq5151 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5151
  have eq5181 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0)) := by
    intro X0
    first
    | exact superpose eq1749 eq5170
    | exact resolve eq5170 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5170
  have eq5190 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq2819 eq5181
    | exact resolve eq5181 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5181
  have eq5195 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1563 eq5190
    | exact resolve eq5190 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5190
  have eq5280 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3867 eq724
    | exact resolve eq724 eq3867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5281 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ (M.op x y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq3867 eq721
    | exact resolve eq721 eq3867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5322 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq55 eq3887
    | exact resolve eq3887 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5328 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ x) (σ (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq3887 (M.op (M.op sF2 sF1) x)
       have i₂ := eq727 sF2 sF1 x
       grind)
    | exact superpose eq727 eq3887
    | exact resolve eq3887 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5349 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq1749 eq5322
    | exact resolve eq5322 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5322
  have eq5358 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq2819 eq5349
    | exact resolve eq5349 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349
  have eq5377 : (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq1076 eq3890
    | exact resolve eq3890 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq3890
  have eq5399 : (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq5377
    | exact resolve eq5377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5377
  have eq5409 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq3867 eq3990
    | exact resolve eq3990 eq3867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3867
  have eq5684 : (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq5328 eq260
    | exact resolve eq260 eq5328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5328
  have eq5782 : (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq4846 eq5684
    | exact resolve eq5684 eq4846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5684
  have eq7469 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq964 eq106
    | (have j0 := eq106 X0
       grind)
    | exact resolve eq106 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq7517 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq160 eq7469
    | exact resolve eq7469 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq7544 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq7469
    | (have j0 := eq7469 (M.op x y)
       grind)
    | exact resolve eq7469 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7469
  have eq7567 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq105 eq7544
    | exact resolve eq7544 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7544
  have eq7576 : (M.op (σ x) (σ y)) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2325 eq7517
    | exact resolve eq7517 eq2325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325 eq7517
  have eq7586 : (M.op (σ x) (σ y)) = (σ (k y (M.op y (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1562 eq7576
    | exact resolve eq7576 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7576
  have eq7591 : (M.op (σ x) (σ y)) = (σ (k y (M.op x x))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1195 eq7586
    | exact resolve eq7586 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7586
  have eq11068 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ x)) = (M.op X0 (M.op (M.op X0 (M.op (σ (M.op x y)) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq2661 eq14
    | exact resolve eq14 eq2661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2661
  have eq11102 : (M.op (σ (M.op x y)) (σ x)) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq260 eq11068
    | exact resolve eq11068 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11068
  have eq11107 : (M.op (σ (M.op x y)) (σ x)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5399 eq11102
    | exact resolve eq11102 eq5399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5399 eq11102
  have eq14574 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | exact superpose eq30 eq305
    | exact resolve eq305 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq305
  have eq14631 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | exact superpose eq37 eq14574
    | (have j0 := eq14574 X0
       grind)
    | exact resolve eq14574 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq14574
  have eq14644 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq14631 X0
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq14631
    | (have j0 := eq14631 X0
       grind)
    | exact resolve eq14631 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq14631
  have eq16318 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X1 (M.op (M.op X0 (M.op (M.op (σ y) (M.op (σ y) X0)) X1)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq1563 eq580
    | exact resolve eq580 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq16595 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (M.op (σ y) (M.op (σ y) (σ x))) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq724 eq16318
    | exact resolve eq16318 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq16318
  have eq16709 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq3208 eq16595
    | exact resolve eq16595 eq3208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3208 eq16595
  have eq16754 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq5195 eq16709
    | exact resolve eq16709 eq5195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16709
  have eq16781 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1345 eq16754
    | exact resolve eq16754 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345 eq16754
  have eq16798 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq16781 X0
       have i₂ := eq598 X0 sF2 sF2
       grind)
    | exact superpose eq598 eq16781
    | exact resolve eq16781 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16781
  have eq16824 : (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ y)) (σ y))) := by
    first
    | exact superpose eq5782 eq16798
    | exact resolve eq16798 eq5782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5782
  have eq16875 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (M.op X0 (σ y))))) := by
    intro X0
    first
    | exact superpose eq16798 eq727
    | exact resolve eq727 eq16798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq16957 : (M.op (σ x) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2410 eq16824
    | exact resolve eq16824 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410 eq16824
  have eq16983 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq11107 eq16957
    | exact resolve eq16957 eq11107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16957
  have eq17016 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x)))) := by
    first
    | exact superpose eq16983 eq3887
    | exact resolve eq3887 eq16983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887 eq16983
  have eq26470 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1)) = (M.op (σ y) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq3602 eq690
    | exact resolve eq690 eq3602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq3602
  have eq26471 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ y) X0)) X1)) = (M.op (σ y) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1563 eq26470
    | exact resolve eq26470 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26470
  have eq26690 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op (σ x) (M.op X0 (σ y)))))) := by
    intro X0
    first
    | exact superpose eq16875 eq3289
    | exact resolve eq3289 eq16875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26854 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op X0 (σ y)))))) := by
    intro X0
    first
    | exact superpose eq5195 eq26690
    | exact resolve eq26690 eq5195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26690
  have eq26957 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ y) (M.op X0 (σ y)))))) := by
    intro X0
    first
    | exact superpose eq5195 eq26854
    | exact resolve eq26854 eq5195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5195 eq26854
  have eq26992 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq3990 eq26957
    | exact resolve eq26957 eq3990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3990 eq26957
  have eq27061 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq55 eq26471
    | exact resolve eq26471 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq26471
  have eq27392 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq964 eq27061
    | exact resolve eq27061 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27061
  have eq27446 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq263 eq27392
    | exact resolve eq27392 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq27392
  have eq27483 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (M.op (σ y) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1563 eq27446
    | exact resolve eq27446 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27446
  have eq27511 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq964 eq27483
    | exact resolve eq27483 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27483
  have eq27530 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1749 eq27511
    | exact resolve eq27511 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749 eq27511
  have eq27538 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq2819 eq27530
    | exact resolve eq27530 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27530
  have eq28243 : ∀ X0 : G, (M.op (M.op (M.op X0 x) X0) y) = (M.op (σ y) (M.op (σ x) (M.op (σ y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3289 eq693
    | exact resolve eq693 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq3289
  have eq28542 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) X0) y) := by
    intro X0
    first
    | exact superpose eq1075 eq28243
    | exact resolve eq28243 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq28243
  have eq28762 : (M.op x y) = (M.op (M.op (M.op (σ x) x) (M.op (σ (M.op x y)) (σ (M.op x y)))) y) := by
    first
    | exact superpose eq2819 eq28542
    | exact resolve eq28542 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2819 eq28542
  have eq66980 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq26992 (M.op x sF3)
       have i₂ := eq598 sF4 x sF3
       grind)
    | exact superpose eq598 eq26992
    | exact resolve eq26992 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26992
  have eq77517 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op X4 (M.op (M.op X1 (M.op X2 X4)) X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq597 X0 X1 X2 x X4 x
       have i₂ := eq594 X4 X1 X2 x x
       grind)
    | exact superpose eq594 eq597
    | exact resolve eq597 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq597
  have eq77988 : (M.op (σ (M.op x y)) (M.op x y)) = (M.op (M.op (σ x) x) (M.op (σ (M.op x y)) y)) := by
    first
    | exact superpose eq28762 eq77517
    | exact resolve eq77517 eq28762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28762
  have eq92095 : y = (M.op (M.op (σ (M.op x y)) (M.op (σ x) x)) (M.op (σ (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq77988 eq721
    | exact resolve eq721 eq77988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77988
  have eq109408 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op y X1) (M.op (M.op (M.op X0 (M.op x y)) (M.op X2 (M.op (M.op X2 x) X1))) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq738 X2 x X1 X0 y X3
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq738
    | (have j0 := eq738 X2 x X1 X0 y X3
       grind)
    | exact resolve eq738 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq738
  have eq111602 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op y X1) (M.op (M.op (M.op X0 (M.op x y)) (M.op y (M.op y X1))) X3))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq109408 X0 X1 x X3
       have i₂ := eq2659 X1 x
       grind)
    | exact superpose eq2659 eq109408
    | exact resolve eq109408 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659 eq109408
  have eq112070 : ∀ X0 X3 : G, (M.op X0 (M.op (M.op X0 (M.op x y)) (M.op y X3))) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq111602 X0 x X0
       have i₂ := eq77517 X0 (M.op X0 sF0) y (M.op y x)
       grind)
    | exact superpose eq77517 eq111602
    | exact resolve eq111602 eq77517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77517 eq111602
  have eq112507 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op y (M.op X1 (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq112070 X0 (M.op (M.op y (M.op X0 sF0)) x)
       have i₂ := eq727 y (M.op X0 sF0) x
       grind)
    | exact superpose eq727 eq112070
    | exact resolve eq112070 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq112070
  have eq113682 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (M.op (M.op y (M.op X0 (M.op x y))) (σ y))))) := by
    intro X0
    first
    | exact superpose eq112507 eq16875
    | exact resolve eq16875 eq112507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16875
  have eq113762 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op y (M.op X0 (M.op x y))) (σ y))))) := by
    intro X0
    first
    | exact superpose eq5409 eq113682
    | exact resolve eq113682 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113682
  have eq114052 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 (σ y))))) := by
    intro X0
    first
    | exact superpose eq112507 eq113762
    | exact resolve eq113762 eq112507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112507 eq113762
  have eq128811 : (σ y) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y)))) (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq114052 eq5280
    | exact resolve eq5280 eq114052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5280
  have eq128873 : (σ y) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y)))) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq11107 eq128811
    | exact resolve eq128811 eq11107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11107 eq128811
  have eq129151 : (σ y) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq5358 eq128873
    | exact resolve eq128873 eq5358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5358 eq128873
  have eq182856 : (M.op (M.op (M.op (σ (M.op x y)) (σ x)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq129151 eq260
    | exact resolve eq260 eq129151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq129151
  have eq183082 : (M.op (M.op (M.op (σ (M.op x y)) (σ x)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq964 eq182856
    | exact resolve eq182856 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq182856
  have eq183165 : (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq5281 eq183082
    | exact resolve eq183082 eq5281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5281 eq183082
  have eq183205 : (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq4846 eq183165
    | exact resolve eq183165 eq4846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4846 eq183165
  have eq238648 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) = (M.op (σ x) (M.op X0 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq183205 eq729
    | exact resolve eq729 eq183205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq183205
  have eq238922 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq2387 eq238648
    | exact resolve eq238648 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387 eq238648
  have eq238995 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (σ y) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq1563 eq238922
    | exact resolve eq238922 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238922
  have eq266709 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq14644 sF0
       grind)
    | exact superpose eq14644 eq105
    | (have j1 := eq14644 (M.op x y)
       grind)
    | exact resolve eq105 eq14644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq266794 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1500 eq266709
    | exact resolve eq266709 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500 eq266709
  have eq266804 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq266794
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq266794
    | exact resolve eq266794 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266794
  have eq266814 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7567 eq266804
    | exact resolve eq266804 eq7567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7567 eq266804
  have eq267005 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq266814 eq114052
    | exact resolve eq114052 eq266814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114052 eq266814
  have eq267206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq17016 eq267005
    | exact resolve eq267005 eq17016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17016 eq267005
  have eq267273 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq267206
       have r₂ := eq28
       grind)
    | exact resolve eq267206 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267206
  have eq267353 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq267273 eq29
    | exact resolve eq29 eq267273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq267273
  have eq267576 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq267353
    | exact resolve eq267353 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267353
  have eq267577 : x = (M.op x y) := by grind
  clear eq267576
  have eq267631 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq267577 eq21
    | exact resolve eq21 eq267577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267697 : y = (M.op (M.op (σ (M.op x y)) (M.op (σ x) x)) (M.op (σ (M.op x y)) x)) := by
    first
    | exact superpose eq267577 eq92095
    | exact resolve eq92095 eq267577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92095
  have eq267748 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq267631
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq267631
    | exact resolve eq267631 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267631
  have eq267768 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq267748 eq27
    | exact resolve eq27 eq267748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq271199 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (M.op X1 X0)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq27538 eq2025
    | exact resolve eq2025 eq27538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq271200 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (M.op X1 X0)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq5409 eq271199
    | exact resolve eq271199 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271199
  have eq271201 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) = (M.op (M.op (σ (M.op x y)) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq267748 eq271200
    | exact resolve eq271200 eq267748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271200
  have eq276821 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ y) X0)) (M.op (σ (M.op x y)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq267748 eq2270
    | exact resolve eq2270 eq267748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq276822 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) X0)) (M.op (σ (M.op x y)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq27538 eq276821
    | exact resolve eq276821 eq27538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27538 eq276821
  have eq276823 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (M.op (σ (M.op x y)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq5409 eq276822
    | exact resolve eq276822 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5409 eq276822
  have eq279507 : (M.op (σ x) (σ y)) = (σ (k y (M.op x x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq267748 eq7591
    | exact resolve eq7591 eq267748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7591
  have eq279526 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op X0 (σ y))) = (M.op (M.op (σ y) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq267748 eq238995
    | exact resolve eq238995 eq267748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238995
  have eq283814 : y = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) x)) (M.op (σ (M.op x y)) x)) := by
    first
    | exact superpose eq267748 eq267697
    | exact resolve eq267697 eq267748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267697
  have eq304317 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq279526 (M.op x sF3)
       have i₂ := eq598 sF1 x sF3
       grind)
    | exact superpose eq598 eq279526
    | exact resolve eq279526 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq279526
  have eq337062 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op X0 (σ y)) (σ y)))) = (M.op (M.op (σ (M.op x y)) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq66980 eq271201
    | exact resolve eq271201 eq66980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66980 eq271201
  have eq337811 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op X0 (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq267768 eq337062
    | exact resolve eq337062 eq267768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267768 eq337062
  have eq338369 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq304317 eq337811
    | exact resolve eq337811 eq304317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304317 eq337811
  have eq338739 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1563 eq338369
    | exact resolve eq338369 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq338369
  have eq339363 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq338739 eq721
    | exact resolve eq721 eq338739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338739
  have eq360599 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x x) y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq14644 (M.op x x)
       have i₂ := eq279507
       grind)
    | exact superpose eq279507 eq14644
    | (have j0 := eq14644 (M.op x x)
       grind)
    | exact resolve eq14644 eq279507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14644 eq279507
  have eq360686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq360599
       have i₂ := eq2009
       grind)
    | exact superpose eq2009 eq360599
    | exact resolve eq360599 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009 eq360599
  have eq360706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq360686
    | exact resolve eq360686 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq360686
  have eq360721 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq360706
       have r₂ := eq28
       grind)
    | exact resolve eq360706 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360706
  have eq360759 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq360721 eq181
    | exact resolve eq181 eq360721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq360721
  have eq361131 : (τ (σ (M.op x y))) = (M.op y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1562 eq360759
    | exact resolve eq360759 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq360759
  have eq361187 : (τ (σ (M.op x y))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1195 eq361131
    | exact resolve eq361131 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq361131
  have eq361214 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31 eq361187
    | exact resolve eq361187 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq361187
  have eq361228 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq267577 eq361214
    | exact resolve eq361214 eq267577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267577 eq361214
  have eq361229 : x = (M.op x x) := by grind
  clear eq361228
  have eq361495 : x = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) x)) (M.op (σ (M.op x y)) x)) := by
    first
    | (have i₁ := eq276823 x x
       have i₂ := eq361229
       grind)
    | exact superpose eq361229 eq276823
    | exact resolve eq276823 eq361229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276823 eq361229
  have eq361499 : x = y := by
    first
    | exact superpose eq283814 eq361495
    | exact resolve eq361495 eq283814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283814 eq361495
  have eq361902 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq361499
       grind)
    | exact superpose eq361499 eq25
    | exact resolve eq25 eq361499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq361499
  have eq362193 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq361902
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq361902
    | exact resolve eq361902 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq361902
  have eq362279 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq267748 eq362193
    | exact resolve eq362193 eq267748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267748 eq362193
  have eq362541 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq362279 eq339363
    | exact resolve eq339363 eq362279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339363 eq362279
  have eq362543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq362541 x
       have i₂ := eq721 sF1 x sF1
       grind)
    | exact superpose eq721 eq362541
    | exact resolve eq362541 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq362541
  have eq362688 : False := by grind
  exact eq362688

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
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
  have eq56 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq94 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq90
  have eq95 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  clear eq89
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq521 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq521 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq58 X2 X1 X4 X0
       grind)
    | exact superpose eq58 eq521
    | exact resolve eq521 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1091 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1033 x X1 X2 X4 X3
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq1033
    | exact resolve eq1033 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq10765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq10765
    | exact resolve eq10765 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10765
  have eq10777 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq10766
       have r₂ := eq28
       grind)
    | exact resolve eq10766 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10766
  have eq10781 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq10777
    | exact resolve eq10777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10777
  have eq10793 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10781 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10781
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq10781
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10781
       grind)
    | exact resolve eq12 eq10781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10794 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10781 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10781
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq10781
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10781
       grind)
    | exact resolve eq12 eq10781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10781
  have eq10818 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq10794
  have eq10819 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq10793
  have eq10826 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq10818
       have r₂ := eq27
       grind)
    | exact resolve eq10818 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10818
  have eq10827 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq10819
       have r₂ := eq27
       grind)
    | exact resolve eq10819 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10819
  have eq11088 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10826 eq104
    | exact resolve eq104 eq10826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq10826
  have eq11097 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11088
  have eq11115 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11097 eq70
    | exact resolve eq70 eq11097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11097
  have eq11163 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq11115
    | exact resolve eq11115 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq11115
  have eq11368 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10827 eq62
    | exact resolve eq62 eq10827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq10827
  have eq11385 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq129 eq11368
    | exact resolve eq11368 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq11368
  have eq11415 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq11385
       grind)
    | exact superpose eq11385 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq11385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11385
  have eq11416 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq11415
  have eq11418 : (M.op x y) = (M.op y x) ∨ (M.op y x) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq11416
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11416
    | exact resolve eq11416 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11416
  have eq11419 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11418
  have eq11652 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq11419
       grind)
    | exact superpose eq11419 eq14
    | exact resolve eq14 eq11419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11419
  have eq11690 : x = y ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11652 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq11652
    | exact resolve eq11652 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11652
  have eq11691 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11690
  have eq11718 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq11691
       grind)
    | exact superpose eq11691 eq53
    | exact resolve eq53 eq11691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq11719 : y = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56 y
       have i₂ := eq11691
       grind)
    | exact superpose eq11691 eq56
    | exact resolve eq56 eq11691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq11691
  have eq11793 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq11718 eq1091
    | exact resolve eq1091 eq11718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq11718
  have eq15309 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq11719 eq11793
    | exact resolve eq11793 eq11719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11719 eq11793
  have eq15466 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq15309 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15309
  have eq15498 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11163
       have i₂ := eq15466 x
       grind)
    | exact superpose eq15466 eq11163
    | exact resolve eq11163 eq15466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11163 eq15466
  have eq15601 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15498
  have eq15758 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq521 x X0 x
       have i₂ := eq15601
       grind)
    | exact superpose eq15601 eq521
    | exact resolve eq521 eq15601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq15601
  have eq15776 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq523 eq15758
    | exact resolve eq15758 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq15758
  have eq15777 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq15776
  have eq16088 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq15777 eq30
    | exact resolve eq30 eq15777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15777
  have eq16200 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq16088
    | exact resolve eq16088 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16088
  have eq16201 : x = y := by grind
  clear eq16200
  have eq16220 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq16201
       grind)
    | exact superpose eq16201 eq19
    | exact resolve eq19 eq16201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq16221 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq16201
       grind)
    | exact superpose eq16201 eq25
    | exact resolve eq25 eq16201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16201
  have eq16330 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16221
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16221
    | exact resolve eq16221 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16221
  have eq16345 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16330 eq27
    | exact resolve eq27 eq16330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16330
  have eq16582 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq16345 eq70
    | exact resolve eq70 eq16345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq16345
  have eq16650 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16582
       have i₂ := eq16220
       grind)
    | exact superpose eq16220 eq16582
    | exact resolve eq16582 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16220 eq16582
  have eq16659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16650 eq15
    | exact resolve eq15 eq16650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16650
  have eq16705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16659
    | exact resolve eq16659 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16659
  have eq16714 : False := by grind
  exact eq16714
