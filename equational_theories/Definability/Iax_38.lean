import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation854 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq98 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq94 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq94 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq94 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq98 (σ X0) (σ X1)
       grind)
    | exact superpose eq98 eq13
    | exact resolve eq13 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq114
    | exact resolve eq114 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq114
  have eq1334 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq121 x y
       grind)
    | exact superpose eq121 eq14
    | (have r₁ := eq14
       have r₂ := eq121 x y
       grind)
    | exact resolve eq14 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1367 : False := by grind
  exact eq1367

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_x_pyx_Equation854 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = X1 ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X1 X2
       have i₂ := eq12 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X0 X2) (M.op X1 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 X2) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq52
    | exact resolve eq52 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq52 X1 (τ X0)
       grind)
    | exact superpose eq52 eq16
    | (have j1 := eq52 X1 (τ X0)
       grind)
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0 X0 x x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0)))))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 X1 X0 (M.op X0 X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq21
    | exact resolve eq21 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq8
    | exact resolve eq8 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 (M.op X0 X1) X0 X1
       have i₂ := eq99 (M.op X0 X1)
       grind)
    | exact superpose eq99 eq22
    | exact resolve eq22 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq142 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X0 X2) X0)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op X0 X2) X0)
       have i₂ := eq126 X0 X2
       grind)
    | exact superpose eq126 eq8
    | exact resolve eq8 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq298 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44 X0 X0 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq44
    | exact resolve eq44 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X1 (M.op X0 (M.op X2 (M.op X3 (M.op X0 X4))))))) = X1 ∨ (M.op X3 (M.op X0 X4)) = (k (M.op X0 X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X2 X1 X0 (M.op X3 (M.op X0 X4))
       have i₂ := eq44 X3 X0 X4
       grind)
    | exact superpose eq44 eq21
    | (have j1 := eq44 X2 X1 (M.op X0 (M.op X2 (M.op X3 (M.op X0 X4))))
       grind)
    | exact resolve eq21 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq330 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 (M.op X1 X0)
       have i₂ := eq8 X0 X1 X0
       grind)
    | exact superpose eq8 eq110
    | exact resolve eq110 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq330 X1 X0
       grind)
    | exact superpose eq330 eq11
    | (have j0 := eq11 X1 X0
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq330 X0 X0
       grind)
    | exact resolve eq11 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq578 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) = X2 ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (σ X1) (σ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq8
    | (have j1 := eq49 X1 X0
       grind)
    | exact resolve eq8 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1135 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1135 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1135
    | (have j0 := eq1135 X0 X1
       grind)
    | exact resolve eq1135 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1215 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq14
    | (have j1 := eq65 y x
       grind)
    | exact resolve eq14 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1365 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq536 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq536 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq536
    | (have j0 := eq536 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq536 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq536 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq536 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1380 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq536 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq1384 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1365 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1559 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1380 (σ X0)
       grind)
    | exact superpose eq1380 eq28
    | exact resolve eq28 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1560 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1380 (τ X0)
       grind)
    | exact superpose eq1380 eq15
    | exact resolve eq15 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq1380
  have eq1561 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1560 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1560
    | exact resolve eq1560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq1562 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1559 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1559
    | exact resolve eq1559 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq2504 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1384 X0 (M.op X0 X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq1384
    | exact resolve eq1384 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq3250 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq639 (τ X1) (τ X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq639
    | (have j0 := eq639 (τ X1) (τ X0)
       grind)
    | exact resolve eq639 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq3276 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3250 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3250
    | (have j0 := eq3250 X0 X1
       grind)
    | exact resolve eq3250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3250
  have eq3281 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3276 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3276
    | (have j0 := eq3276 X0 X1
       grind)
    | exact resolve eq3276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3276
  have eq3282 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3281 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3281
    | (have j0 := eq3281 X0 X1
       grind)
    | exact resolve eq3281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281
  have eq3283 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3282 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3282
    | (have j0 := eq3282 X0 X1
       grind)
    | exact resolve eq3282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3282
  have eq3298 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq3283 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq1561 X0
       grind)
    | exact superpose eq1561 eq3283
    | (have j0 := eq3283 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq3283 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3300 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq3283 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq1562 X0
       grind)
    | exact superpose eq1562 eq3283
    | (have j0 := eq3283 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq3283 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1215
       have i₂ := eq1194 x y
       grind)
    | exact superpose eq1194 eq1215
    | (have j1 := eq1194 x y
       grind)
    | (have r₁ := eq1215
       have r₂ := eq1194 x y
       grind)
    | exact resolve eq1215 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq1215
  have eq7252 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq7251
  have eq7497 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq7252
       grind)
    | exact superpose eq7252 eq9
    | exact resolve eq9 eq7252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7252
  have eq7541 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq7497
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq7497
    | exact resolve eq7497 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7497
  have eq7542 : y = (k y x) := by
    first
    | (have j1 := eq71 y x
       grind)
    | (have r₁ := eq7541
       have r₂ := eq71 y x
       grind)
    | exact resolve eq7541 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq7541
  have eq7847 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7542
       grind)
    | exact superpose eq7542 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq7542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7851 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3283 y x
       have i₂ := eq7542
       grind)
    | exact superpose eq7542 eq3283
    | (have j0 := eq3283 y x
       grind)
    | exact resolve eq3283 eq7542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3283
  have eq7869 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 (σ (τ X0))))) = X2 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq578 (τ X0) (τ X1) X2
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq578
    | (have j0 := eq578 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq578 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq7872 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq578 y x X0
       have i₂ := eq7542
       grind)
    | exact superpose eq7542 eq578
    | (have j0 := eq578 y x x
       grind)
    | exact resolve eq578 eq7542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq7987 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 X0))) = X2 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7869 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7869
    | (have j0 := eq7869 X0 X1 X2
       grind)
    | exact resolve eq7869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7869
  have eq7991 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7987 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7987
    | (have j0 := eq7987 X0 X1 X2
       grind)
    | exact resolve eq7987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7987
  have eq7992 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7991 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7991
    | (have j0 := eq7991 X0 X1 X2
       grind)
    | exact resolve eq7991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7991
  have eq7993 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7992 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7992
    | (have j0 := eq7992 X0 X1 X2
       grind)
    | exact resolve eq7992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7992
  have eq17922 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X3 X4) (M.op X2 X0))))) = X1 ∨ (k (M.op (M.op X3 X4) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq310 (M.op X1 X2) X1 X2 X0 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq310
    | exact resolve eq310 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq30176 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2504 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504
  have eq30182 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq30176 X0
       have j1 := eq298 X0
       grind)
    | (have r₁ := eq30176 X0
       have r₂ := eq298 X0
       grind)
    | exact resolve eq30176 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq30176
  have eq30536 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq30182 (σ X0)
       grind)
    | exact superpose eq30182 eq20
    | exact resolve eq20 eq30182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq30541 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq30182 (τ X0)
       grind)
    | exact superpose eq30182 eq16
    | exact resolve eq16 eq30182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq30182
  have eq30546 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30541 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30541
    | exact resolve eq30541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30541
  have eq30550 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30536 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq30536
    | exact resolve eq30536 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30536
  have eq31706 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 (σ (M.op (τ X0) (τ X0))) X0
       have i₂ := eq30546 X0
       grind)
    | exact superpose eq30546 eq52
    | exact resolve eq52 eq30546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30546
  have eq32176 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq30550 X0
       grind)
    | exact superpose eq30550 eq52
    | exact resolve eq52 eq30550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq30550
  have eq112241 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 (k X0 X1)
       have i₂ := eq7993 X0 X1 X0
       grind)
    | exact superpose eq7993 eq110
    | (have j1 := eq7993 X0 X1 x
       grind)
    | exact resolve eq110 eq7993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7993
  have eq112377 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq112241 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq1561 X0
       grind)
    | exact superpose eq1561 eq112241
    | (have j0 := eq112241 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq112241 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq112378 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq112241 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq1562 X0
       grind)
    | exact superpose eq1562 eq112241
    | (have j0 := eq112241 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq112241 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq112407 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq112241 y x
       have i₂ := eq7542
       grind)
    | exact superpose eq7542 eq112241
    | (have j0 := eq112241 y x
       grind)
    | exact resolve eq112241 eq7542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112241
  have eq112505 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq112407
       have r₂ := eq7851
       grind)
    | exact resolve eq112407 eq7851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7851 eq112407
  have eq112507 : ∀ X0 : G, (M.op X0 X0) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq112378 X0
       have j1 := eq3300 X0
       grind)
    | (have r₁ := eq112378 X0
       have r₂ := eq3300 X0
       grind)
    | exact resolve eq112378 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300 eq112378
  have eq112508 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq112377 X0
       have j1 := eq3298 X0
       grind)
    | (have r₁ := eq112377 X0
       have r₂ := eq3298 X0
       grind)
    | exact resolve eq112377 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298 eq112377
  have eq114356 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq112507 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112507
    | exact resolve eq112507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112507
  have eq114614 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq112508 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112508
    | exact resolve eq112508 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114749 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1 (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))
       have i₂ := eq112508 (M.op X0 X0)
       grind)
    | exact superpose eq112508 eq108
    | exact resolve eq108 eq112508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq112508
  have eq114793 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) (M.op X1 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq114749 X0 X1
       have i₂ := eq8 X0 X0 X0
       grind)
    | exact superpose eq8 eq114749
    | exact resolve eq114749 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114749
  have eq115180 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (M.op (M.op X1 (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (τ (M.op X0 X0)) X1 (τ X0)
       have i₂ := eq114356 X0
       grind)
    | exact superpose eq114356 eq8
    | exact resolve eq8 eq114356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115409 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq114614 y
       have i₂ := eq112505
       grind)
    | exact superpose eq112505 eq114614
    | exact resolve eq114614 eq112505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115441 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ (M.op X0 X0)) X1 (σ X0)
       have i₂ := eq114614 X0
       grind)
    | exact superpose eq114614 eq8
    | exact resolve eq8 eq114614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134441 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) = X0 ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17922 X0 X0 (M.op X0 X1) X0 X1
       have i₂ := eq142 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq142 eq17922
    | (have j0 := eq17922 X0 X1 x X0 X1
       grind)
    | exact resolve eq17922 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq17922
  have eq146435 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) = (M.op (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) X0) := by
    intro X0
    first
    | (have i₁ := eq110 X0 (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))
       have i₂ := eq114793 X0 X0
       grind)
    | exact superpose eq114793 eq110
    | exact resolve eq110 eq114793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147683 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31706 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31706
    | exact resolve eq31706 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31706
  have eq148366 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32176 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32176
    | exact resolve eq32176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32176
  have eq247682 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq21 (τ X0) (τ (M.op X0 X0)) x (τ X0)
       have i₂ := eq115180 X0 x
       grind)
    | exact superpose eq115180 eq21
    | exact resolve eq21 eq115180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115180
  have eq247741 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq247682 X0
       have i₂ := eq148366 X0
       grind)
    | exact superpose eq148366 eq247682
    | (have j1 := eq148366 X0
       grind)
    | exact resolve eq247682 eq148366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148366 eq247682
  have eq247754 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq247741 X0
       have i₂ := eq114356 X0
       grind)
    | exact superpose eq114356 eq247741
    | (have j0 := eq247741 X0
       grind)
    | exact resolve eq247741 eq114356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114356 eq247741
  have eq247846 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq247754 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq247754
    | exact resolve eq247754 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247754
  have eq248261 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq247846 X0
       grind)
    | exact superpose eq247846 eq10
    | (have j1 := eq247846 X0
       grind)
    | exact resolve eq10 eq247846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247846
  have eq248409 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq248261 X0
       grind)
    | exact superpose eq248261 eq10
    | (have j1 := eq248261 X0
       grind)
    | exact resolve eq10 eq248261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248261
  have eq248561 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq248409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248409
  have eq250370 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0) (σ (M.op X0 X0)) x (σ X0)
       have i₂ := eq115441 X0 x
       grind)
    | exact superpose eq115441 eq21
    | exact resolve eq21 eq115441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq115441
  have eq250438 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq250370 y
       have i₂ := eq112505
       grind)
    | exact superpose eq112505 eq250370
    | exact resolve eq250370 eq112505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250444 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq250370 X0
       have i₂ := eq147683 X0
       grind)
    | exact superpose eq147683 eq250370
    | (have j1 := eq147683 X0
       grind)
    | exact resolve eq250370 eq147683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147683 eq250370
  have eq250457 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq250444 X0
       have i₂ := eq114614 X0
       grind)
    | exact superpose eq114614 eq250444
    | (have j0 := eq250444 X0
       grind)
    | exact resolve eq250444 eq114614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114614 eq250444
  have eq250537 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq250457 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq250457
    | exact resolve eq250457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250457
  have eq251038 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (τ X0) (τ X0))
       have i₂ := eq250537 X0
       grind)
    | exact superpose eq250537 eq9
    | (have j1 := eq250537 X0
       grind)
    | exact resolve eq9 eq250537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250537
  have eq251144 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (τ X0) (τ X0))
       have i₂ := eq251038 X0
       grind)
    | exact superpose eq251038 eq9
    | (have j1 := eq251038 X0
       grind)
    | exact resolve eq9 eq251038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251038
  have eq251264 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq251144 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq251144
    | exact resolve eq251144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251286 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq99 (τ X0)
       have i₂ := eq251144 X0
       grind)
    | exact superpose eq251144 eq99
    | (have j1 := eq251144 X0
       grind)
    | exact resolve eq99 eq251144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251144
  have eq251408 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq251264 X0
       grind)
    | exact superpose eq251264 eq10
    | (have j1 := eq251264 X0
       grind)
    | exact resolve eq10 eq251264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251264
  have eq251560 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 (σ X0)
       have i₂ := eq251408 X0
       grind)
    | exact superpose eq251408 eq99
    | (have j1 := eq251408 X0
       grind)
    | exact resolve eq99 eq251408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq251408
  have eq251737 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq251560 y
       have i₂ := eq7847
       grind)
    | exact superpose eq7847 eq251560
    | exact resolve eq251560 eq7847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7847 eq251560
  have eq251771 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq251737
  have eq251797 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq250438
       have i₂ := eq251771
       grind)
    | exact superpose eq251771 eq250438
    | exact resolve eq250438 eq251771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250438 eq251771
  have eq251830 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq251797
       have i₂ := eq115409
       grind)
    | exact superpose eq115409 eq251797
    | exact resolve eq251797 eq115409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115409 eq251797
  have eq252048 : (τ y) = (M.op (τ y) (τ (M.op x y))) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq251286 y
       have i₂ := eq112505
       grind)
    | exact superpose eq112505 eq251286
    | (have j0 := eq251286 y
       grind)
    | exact resolve eq251286 eq112505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251286
  have eq325746 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq110 (σ y) (σ y)
       have i₂ := eq7872 (σ y)
       grind)
    | exact superpose eq7872 eq110
    | exact resolve eq110 eq7872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq7872
  have eq325754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq325746
       have i₂ := eq251830
       grind)
    | exact superpose eq251830 eq325746
    | exact resolve eq325746 eq251830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251830 eq325746
  have eq325782 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq325754
       have r₂ := eq14
       grind)
    | exact resolve eq325754 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325754
  have eq325806 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq325782
       grind)
    | exact superpose eq325782 eq9
    | exact resolve eq9 eq325782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325782
  have eq325877 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq325806
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq325806
    | exact resolve eq325806 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325806
  have eq325878 : y = (M.op x y) := by grind
  clear eq325877
  have eq326029 : (τ y) = (M.op (τ y) (τ y)) ∨ (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have i₁ := eq252048
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq252048
    | exact resolve eq252048 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252048
  have eq326455 : x = (M.op x (M.op (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) y)) := by
    first
    | (have i₁ := eq114793 y x
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq114793
    | exact resolve eq114793 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114793
  have eq326514 : x = (k (M.op y y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq134441 x y
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq134441
    | exact resolve eq134441 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134441
  have eq326819 : (τ y) = (M.op (τ y) (τ y)) := by grind
  clear eq326029
  have eq326875 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq326514
       have i₂ := eq112505
       grind)
    | exact superpose eq112505 eq326514
    | exact resolve eq326514 eq112505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326514
  have eq326889 : x = (M.op x (σ (M.op (τ (M.op y y)) (τ (M.op y y))))) := by
    first
    | (have i₁ := eq326455
       have i₂ := eq146435 y
       grind)
    | exact superpose eq146435 eq326455
    | exact resolve eq326455 eq146435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146435 eq326455
  have eq327056 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq326875
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq326875
    | exact resolve eq326875 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326875
  have eq327060 : x = (M.op x (σ (M.op (τ (M.op x y)) (τ (M.op x y))))) := by
    first
    | (have i₁ := eq326889
       have i₂ := eq112505
       grind)
    | exact superpose eq112505 eq326889
    | exact resolve eq326889 eq112505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112505 eq326889
  have eq327118 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq327056
       have i₂ := eq7542
       grind)
    | exact superpose eq7542 eq327056
    | exact resolve eq327056 eq7542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7542 eq327056
  have eq327119 : x = (M.op x (σ (M.op (τ y) (τ y)))) := by
    first
    | (have i₁ := eq327060
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq327060
    | exact resolve eq327060 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327060
  have eq327138 : x = y ∨ x = y := by
    first
    | (have i₁ := eq327118
       have i₂ := eq325878
       grind)
    | exact superpose eq325878 eq327118
    | exact resolve eq327118 eq325878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325878 eq327118
  have eq327139 : x = y := by grind
  clear eq327138
  have eq327140 : x = (M.op x (σ (τ y))) := by
    first
    | (have i₁ := eq327119
       have i₂ := eq326819
       grind)
    | exact superpose eq326819 eq327119
    | exact resolve eq327119 eq326819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326819 eq327119
  have eq327150 : x = (M.op x y) := by
    first
    | (have i₁ := eq327140
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq327140
    | exact resolve eq327140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327140
  have eq327156 : x = (M.op x x) := by
    first
    | (have i₁ := eq327150
       have i₂ := eq327139
       grind)
    | exact superpose eq327139 eq327150
    | exact resolve eq327150 eq327139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327150
  have eq327158 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq327139
       grind)
    | exact superpose eq327139 eq14
    | exact resolve eq14 eq327139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327139
  have eq327917 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq327158
       have i₂ := eq327156
       grind)
    | exact superpose eq327156 eq327158
    | exact resolve eq327158 eq327156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327158
  have eq329372 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq248561 x
       have i₂ := eq327156
       grind)
    | exact superpose eq327156 eq248561
    | (have j0 := eq248561 x
       grind)
    | exact resolve eq248561 eq327156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248561 eq327156
  have eq330032 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq329372
  have eq330114 : False := by grind
  exact eq330114

/-- `Equation856`: `x = x ◇ ((y ◇ z) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation856 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law856 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law856.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq111 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq111 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq111 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq111 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq115 (σ X0) (σ X1)
       grind)
    | exact superpose eq115 eq13
    | exact resolve eq13 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq131
    | exact resolve eq131 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq131
  have eq1401 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq138 x y
       grind)
    | exact superpose eq138 eq14
    | (have r₁ := eq14
       have r₂ := eq138 x y
       grind)
    | exact resolve eq14 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq1430 : False := by grind
  exact eq1430

/-- `Equation856`: `x = x ◇ ((y ◇ z) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxy_pyx_Equation856 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law856 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law856.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x x) (M.op x X0))
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq22 X0 (M.op X0 X0)
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq42 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq65 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq241 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq9
    | (have j1 := eq44 X1 X0
       grind)
    | exact resolve eq9 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq354 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq411 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq354 (σ X0)
       grind)
    | exact superpose eq354 eq13
    | exact resolve eq13 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq411 X0
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq411
    | exact resolve eq411 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq411
  have eq562 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28 (σ X0)
       have i₂ := eq418 X0
       grind)
    | exact superpose eq418 eq28
    | exact resolve eq28 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1242 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1363 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1242 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1242
    | (have j0 := eq1242 X0 X1
       grind)
    | exact resolve eq1242 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq2223 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq241 X0 X1
       have i₂ := eq418 X0
       grind)
    | exact superpose eq418 eq241
    | (have j0 := eq241 X0 X1
       grind)
    | exact resolve eq241 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq418
  have eq2356 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2223 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq2223
    | (have j0 := eq2223 X0 X1
       grind)
    | exact resolve eq2223 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq8323 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2356 y x
       grind)
    | exact superpose eq2356 eq14
    | (have j1 := eq2356 y x
       grind)
    | exact resolve eq14 eq2356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356
  have eq8441 : x = (M.op y y) := by
    first
    | (have j1 := eq1363 x y
       grind)
    | (have r₁ := eq8323
       have r₂ := eq1363 x y
       grind)
    | exact resolve eq8323 eq1363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363 eq8323
  have eq8743 : x = (M.op x y) := by
    first
    | (have i₁ := eq28 y
       have i₂ := eq8441
       grind)
    | exact superpose eq8441 eq28
    | exact resolve eq28 eq8441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq8754 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq562 y
       have i₂ := eq8441
       grind)
    | exact superpose eq8441 eq562
    | exact resolve eq562 eq8441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq8441
  have eq10169 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq8754
       grind)
    | exact superpose eq8754 eq14
    | exact resolve eq14 eq8754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8754
  have eq10219 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq10169
       have i₂ := eq8743
       grind)
    | exact superpose eq8743 eq10169
    | exact resolve eq10169 eq8743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8743 eq10169
  have eq10220 : False := by grind
  exact eq10220

/-- `Equation856`: `x = x ◇ ((y ◇ z) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation856 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law856 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law856.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x x) (M.op x X0))
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op X0 X0)
       have i₂ := eq18 X0 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq45 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq46 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41
    | exact resolve eq41 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq48 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq30
    | exact resolve eq30 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq88 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq46 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq46
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq125 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq127 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq53
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq139 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq125 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq125
    | exact resolve eq125 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq242 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq24
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq24 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq139
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq139 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq139
  have eq290 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq865 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq48
    | exact resolve eq48 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | (have j1 := eq48 X1 X0
       grind)
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq956 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq865 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq865
    | (have j0 := eq865 X0 X1
       grind)
    | exact resolve eq865 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq1014 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq1016 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq956 X0 X1
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq956 (M.op X0 X0) X1
       grind)
    | exact superpose eq956 eq24
    | (have j1 := eq956 X0 X1
       grind)
    | exact resolve eq24 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1605 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq24
    | (have j1 := eq56 X0 X0
       grind)
    | exact resolve eq24 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq56
  have eq2737 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | (have j0 := eq88 X1 (σ X0)
       grind)
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq2808 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2737 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2737
    | (have j0 := eq2737 X0 X1
       grind)
    | exact resolve eq2737 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq3074 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq252 X0
       have i₂ := eq2808 X0 X0
       grind)
    | exact superpose eq2808 eq252
    | (have j0 := eq252 X0
       have j1 := eq2808 X0 X0
       grind)
    | (have r₁ := eq252 x
       have r₂ := eq2808 x x
       grind)
    | exact resolve eq252 eq2808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2808
  have eq3106 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3074 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074
  have eq6934 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq290 x y
       grind)
    | exact superpose eq290 eq14
    | (have j1 := eq290 x y
       grind)
    | exact resolve eq14 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq7001 : y = (k y x) := by
    first
    | (have j1 := eq1014 x y
       grind)
    | (have r₁ := eq6934
       have r₂ := eq1014 x y
       grind)
    | exact resolve eq6934 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq6934
  have eq7214 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 x y
       have i₂ := eq7001
       grind)
    | exact superpose eq7001 eq36
    | (have j0 := eq36 x y
       grind)
    | exact resolve eq36 eq7001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq7219 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq956 x y
       have i₂ := eq7001
       grind)
    | exact superpose eq7001 eq956
    | (have j0 := eq956 x y
       grind)
    | exact resolve eq956 eq7001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq7220 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1016 x y
       have i₂ := eq7001
       grind)
    | exact superpose eq7001 eq1016
    | (have j0 := eq1016 x y
       grind)
    | exact resolve eq1016 eq7001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq8009 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq7214
       grind)
    | exact superpose eq7214 eq18
    | exact resolve eq18 eq7214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8038 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq9822 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8009
       have i₂ := eq7214
       grind)
    | exact superpose eq7214 eq8009
    | exact resolve eq8009 eq7214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7214 eq8009
  have eq9864 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9822
       have r₂ := eq8038
       grind)
    | exact resolve eq9822 eq8038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8038 eq9822
  have eq10123 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61 y y
       have i₂ := eq9864
       grind)
    | exact superpose eq9864 eq61
    | (have j0 := eq61 y y
       grind)
    | (have r₁ := eq61 y y
       have r₂ := eq9864
       grind)
    | exact resolve eq61 eq9864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq9864
  have eq10144 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq10123
  have eq10789 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq252 y
       have i₂ := eq10144
       grind)
    | exact superpose eq10144 eq252
    | (have j0 := eq252 y
       grind)
    | exact resolve eq252 eq10144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq10144
  have eq10814 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10789
  have eq38126 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq895 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq38127 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq38126 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38126
    | (have j0 := eq38126 X0
       grind)
    | exact resolve eq38126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38126
  have eq38285 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq38127 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq38127
    | (have j0 := eq38127 X0
       have j1 := eq30 X0 X0
       grind)
    | (have r₁ := eq38127 X0
       have r₂ := eq30 X0 X0
       grind)
    | exact resolve eq38127 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq38318 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq38285 X0
       have j1 := eq38127 X0
       grind)
    | (have r₁ := eq38285 X0
       have r₂ := eq38127 X0
       grind)
    | exact resolve eq38285 eq38127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38127 eq38285
  have eq38608 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38318 (σ X0)
       have i₂ := eq3106 X0
       grind)
    | exact superpose eq3106 eq38318
    | (have j0 := eq38318 (σ X0)
       have j1 := eq3106 X0
       grind)
    | (have r₁ := eq38318 (σ X0)
       have r₂ := eq3106 X0
       grind)
    | exact resolve eq38318 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3106 eq38318
  have eq38628 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq38608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38608
  have eq38648 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38628 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38628
    | (have j0 := eq38628 X0
       grind)
    | exact resolve eq38628 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38628
  have eq40875 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq242 x y
       grind)
    | exact superpose eq242 eq14
    | (have j1 := eq242 x y
       grind)
    | exact resolve eq14 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41012 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq41032 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40875
       have i₂ := eq7001
       grind)
    | exact superpose eq7001 eq40875
    | exact resolve eq40875 eq7001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40875
  have eq44812 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq41012 (τ X1) (τ X0)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq41012
    | (have j0 := eq41012 (τ X1) (τ X0)
       grind)
    | exact resolve eq41012 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq44821 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41012 x y
       have i₂ := eq7001
       grind)
    | exact superpose eq7001 eq41012
    | (have j0 := eq41012 x y
       grind)
    | exact resolve eq41012 eq7001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7001 eq41012
  have eq44875 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44812 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq44812
    | (have j0 := eq44812 X0 X1
       grind)
    | exact resolve eq44812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44812
  have eq44888 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44875 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq44875
    | (have j0 := eq44875 X0 X1
       grind)
    | exact resolve eq44875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44875
  have eq44892 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44888 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44888
    | (have j0 := eq44888 X0 X1
       grind)
    | exact resolve eq44888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44888
  have eq44893 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44892 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44892
    | (have j0 := eq44892 X0 X1
       grind)
    | exact resolve eq44892 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44892
  have eq47664 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41032
       have i₂ := eq7220
       grind)
    | exact superpose eq7220 eq41032
    | (have r₁ := eq41032
       have r₂ := eq7220
       grind)
    | exact resolve eq41032 eq7220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47665 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41032
       have i₂ := eq7219
       grind)
    | exact superpose eq7219 eq41032
    | (have r₁ := eq41032
       have r₂ := eq7219
       grind)
    | exact resolve eq41032 eq7219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7219 eq41032
  have eq47669 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq47665
  have eq47670 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq47664
  have eq48317 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq47669
       grind)
    | exact superpose eq47669 eq14
    | exact resolve eq14 eq47669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47669
  have eq50686 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq47670
       grind)
    | exact superpose eq47670 eq14
    | exact resolve eq14 eq47670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50712 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127 (σ x) y
       have i₂ := eq47670
       grind)
    | exact superpose eq47670 eq127
    | (have j0 := eq127 (σ x) y
       grind)
    | exact resolve eq127 eq47670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq47670
  have eq50821 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50712
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq50712
    | exact resolve eq50712 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50712
  have eq50844 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq44893 y x
       grind)
    | (have r₁ := eq50821
       have r₂ := eq44893 y x
       grind)
    | exact resolve eq50821 eq44893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44893 eq50821
  have eq51252 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50686
       have i₂ := eq7220
       grind)
    | exact superpose eq7220 eq50686
    | exact resolve eq50686 eq7220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7220 eq50686
  have eq51258 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq51252
  have eq51955 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10814
       have i₂ := eq50844
       grind)
    | exact superpose eq50844 eq10814
    | exact resolve eq10814 eq50844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10814 eq50844
  have eq52124 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq51955
  have eq52153 : x = (M.op x y) := by
    first
    | (have r₁ := eq52124
       have r₂ := eq51258
       grind)
    | exact resolve eq52124 eq51258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51258 eq52124
  have eq52542 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq48317
       have i₂ := eq52153
       grind)
    | exact superpose eq52153 eq48317
    | exact resolve eq48317 eq52153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48317
  have eq52636 : x = (M.op y y) := by grind
  clear eq52542
  have eq52895 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38648 y
       have i₂ := eq52636
       grind)
    | exact superpose eq52636 eq38648
    | exact resolve eq38648 eq52636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38648 eq52636
  have eq58550 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1605 y
       have i₂ := eq52895
       grind)
    | exact superpose eq52895 eq1605
    | exact resolve eq1605 eq52895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605 eq52895
  have eq58599 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq58550
  have eq58604 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq58599
       have r₂ := eq44821
       grind)
    | exact resolve eq58599 eq44821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44821 eq58599
  have eq59455 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58604
       grind)
    | exact superpose eq58604 eq14
    | exact resolve eq14 eq58604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58604
  have eq59610 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq59455
       have i₂ := eq52153
       grind)
    | exact superpose eq52153 eq59455
    | exact resolve eq59455 eq52153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52153 eq59455
  have eq59611 : False := by grind
  exact eq59611

/-- `Equation856`: `x = x ◇ ((y ◇ z) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation856 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law856 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law856.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x x) (M.op x X0))
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op X0 X0)
       have i₂ := eq18 X0 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq46 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  clear eq17
  have eq55 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq30
    | exact resolve eq30 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq64 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44
    | exact resolve eq44 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq70 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq44
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq75 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq125 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq55 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq55
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq244 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq24
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq24 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq75
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq75 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq75
  have eq293 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq272
    | (have j0 := eq272 X0 X1
       grind)
    | exact resolve eq272 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq870 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq41
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq10
    | (have j1 := eq41 X1 X0
       grind)
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq961 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq870
    | (have j0 := eq870 X0 X1
       grind)
    | exact resolve eq870 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq1019 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq1021 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq961 X0 X1
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq961 (M.op X0 X0) X1
       grind)
    | exact superpose eq961 eq24
    | (have j1 := eq961 X0 X1
       grind)
    | exact resolve eq24 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1611 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ x)
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq24
    | (have j1 := eq56 X0 X0
       grind)
    | exact resolve eq24 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq56
  have eq6178 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq293 x y
       grind)
    | exact superpose eq293 eq14
    | (have j1 := eq293 x y
       grind)
    | exact resolve eq14 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq6243 : y = (k x y) := by
    first
    | (have j1 := eq1019 x y
       grind)
    | (have r₁ := eq6178
       have r₂ := eq1019 x y
       grind)
    | exact resolve eq6178 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq6178
  have eq6507 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 x y
       have i₂ := eq6243
       grind)
    | exact superpose eq6243 eq36
    | (have j0 := eq36 x y
       grind)
    | exact resolve eq36 eq6243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq6511 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq961 x y
       have i₂ := eq6243
       grind)
    | exact superpose eq6243 eq961
    | (have j0 := eq961 x y
       grind)
    | exact resolve eq961 eq6243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq6512 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1021 x y
       have i₂ := eq6243
       grind)
    | exact superpose eq6243 eq1021
    | (have j0 := eq1021 x y
       grind)
    | exact resolve eq1021 eq6243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq7098 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq6507
       grind)
    | exact superpose eq6507 eq18
    | exact resolve eq18 eq6507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7127 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq9202 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7098
       have i₂ := eq6507
       grind)
    | exact superpose eq6507 eq7098
    | exact resolve eq7098 eq6507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6507 eq7098
  have eq9239 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9202
       have r₂ := eq7127
       grind)
    | exact resolve eq9202 eq7127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7127 eq9202
  have eq9491 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61 y y
       have i₂ := eq9239
       grind)
    | exact superpose eq9239 eq61
    | (have j0 := eq61 y y
       grind)
    | (have r₁ := eq61 y y
       have r₂ := eq9239
       grind)
    | exact resolve eq61 eq9239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq9239
  have eq9508 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq9491
  have eq9754 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq254 y
       have i₂ := eq9508
       grind)
    | exact superpose eq9508 eq254
    | (have j0 := eq254 y
       grind)
    | exact resolve eq254 eq9508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq9508
  have eq9779 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9754
  have eq35010 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq900 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq35011 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35010 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35010
    | (have j0 := eq35010 X0
       grind)
    | exact resolve eq35010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35010
  have eq35783 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq35011 (σ X0)
       have i₂ := eq125 X0 (σ X0)
       grind)
    | exact superpose eq125 eq35011
    | (have j0 := eq35011 (σ X0)
       have j1 := eq125 X0 (σ X0)
       grind)
    | (have r₁ := eq35011 (σ X0)
       have r₂ := eq125 X0 (σ X0)
       grind)
    | exact resolve eq35011 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq35011
  have eq35790 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq35783 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35783
  have eq35792 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq35790 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35790
    | (have j0 := eq35790 X0
       grind)
    | exact resolve eq35790 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35790
  have eq35800 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq35792 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35792
    | (have j0 := eq35792 X0
       grind)
    | exact resolve eq35792 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35792
  have eq41688 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq244 x y
       grind)
    | exact superpose eq244 eq14
    | (have j1 := eq244 x y
       grind)
    | exact resolve eq14 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41825 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq244 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq41844 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41688
       have i₂ := eq6243
       grind)
    | exact superpose eq6243 eq41688
    | exact resolve eq41688 eq6243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41688
  have eq42308 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq41825 (τ X0) (τ X1)
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq41825
    | (have j0 := eq41825 (τ X0) (τ X1)
       grind)
    | exact resolve eq41825 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq42323 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41825 x y
       have i₂ := eq6243
       grind)
    | exact superpose eq6243 eq41825
    | (have j0 := eq41825 x y
       grind)
    | exact resolve eq41825 eq6243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6243 eq41825
  have eq42388 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42308 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq42308
    | (have j0 := eq42308 X0 X1
       grind)
    | exact resolve eq42308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42308
  have eq42398 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42388 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42388
    | (have j0 := eq42388 X0 X1
       grind)
    | exact resolve eq42388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42388
  have eq42399 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42398 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq42398
    | (have j0 := eq42398 X0 X1
       grind)
    | exact resolve eq42398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42398
  have eq42400 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42399 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42399
    | (have j0 := eq42399 X0 X1
       grind)
    | exact resolve eq42399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42399
  have eq44312 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41844
       have i₂ := eq6512
       grind)
    | exact superpose eq6512 eq41844
    | (have r₁ := eq41844
       have r₂ := eq6512
       grind)
    | exact resolve eq41844 eq6512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44313 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41844
       have i₂ := eq6511
       grind)
    | exact superpose eq6511 eq41844
    | (have r₁ := eq41844
       have r₂ := eq6511
       grind)
    | exact resolve eq41844 eq6511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6511 eq41844
  have eq44316 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq44313
  have eq44317 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq44312
  have eq45083 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44316
       grind)
    | exact superpose eq44316 eq14
    | exact resolve eq14 eq44316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44316
  have eq46294 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44317
       grind)
    | exact superpose eq44317 eq14
    | exact resolve eq14 eq44317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46319 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70 (σ x) y
       have i₂ := eq44317
       grind)
    | exact superpose eq44317 eq70
    | (have j0 := eq70 (σ x) y
       grind)
    | exact resolve eq70 eq44317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq44317
  have eq46426 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46319
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq46319
    | exact resolve eq46319 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46319
  have eq46449 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq42400 x y
       grind)
    | (have r₁ := eq46426
       have r₂ := eq42400 x y
       grind)
    | exact resolve eq46426 eq42400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42400 eq46426
  have eq46957 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46294
       have i₂ := eq6512
       grind)
    | exact superpose eq6512 eq46294
    | exact resolve eq46294 eq6512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6512 eq46294
  have eq46962 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq46957
  have eq48726 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9779
       have i₂ := eq46449
       grind)
    | exact superpose eq46449 eq9779
    | exact resolve eq9779 eq46449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9779 eq46449
  have eq48889 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq48726
  have eq48915 : x = (M.op x y) := by
    first
    | (have r₁ := eq48889
       have r₂ := eq46962
       grind)
    | exact resolve eq48889 eq46962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46962 eq48889
  have eq49720 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45083
       have i₂ := eq48915
       grind)
    | exact superpose eq48915 eq45083
    | exact resolve eq45083 eq48915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45083
  have eq49813 : x = (M.op y y) := by grind
  clear eq49720
  have eq50116 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35800 y
       have i₂ := eq49813
       grind)
    | exact superpose eq49813 eq35800
    | exact resolve eq35800 eq49813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35800 eq49813
  have eq53476 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1611 y
       have i₂ := eq50116
       grind)
    | exact superpose eq50116 eq1611
    | exact resolve eq1611 eq50116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611 eq50116
  have eq53524 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq53476
  have eq53529 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq53524
       have r₂ := eq42323
       grind)
    | exact resolve eq53524 eq42323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42323 eq53524
  have eq54081 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq53529
       grind)
    | exact superpose eq53529 eq14
    | exact resolve eq14 eq53529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53529
  have eq54235 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq54081
       have i₂ := eq48915
       grind)
    | exact superpose eq48915 eq54081
    | exact resolve eq54081 eq48915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48915 eq54081
  have eq54236 : False := by grind
  exact eq54236

/-- `Equation860`: `x = x ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation860 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law860 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law860.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq95 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq95 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq95 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq95 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq99 (σ X0) (σ X1)
       grind)
    | exact superpose eq99 eq13
    | exact resolve eq13 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 X1
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq115
    | exact resolve eq115 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq115
  have eq1061 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq122 x y
       grind)
    | exact superpose eq122 eq14
    | (have r₁ := eq14
       have r₂ := eq122 x y
       grind)
    | exact resolve eq14 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq1089 : False := by grind
  exact eq1089

/-- `Equation873`: `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation873 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law873 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law873.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq119 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq115 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq115 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq115 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq119 (σ X0) (σ X1)
       grind)
    | exact superpose eq119 eq13
    | exact resolve eq13 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1
       have i₂ := eq119 X0 X1
       grind)
    | exact superpose eq119 eq138
    | exact resolve eq138 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq138
  have eq1343 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq147 x y
       grind)
    | exact superpose eq147 eq14
    | (have r₁ := eq14
       have r₂ := eq147 x y
       grind)
    | exact resolve eq14 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq1370 : False := by grind
  exact eq1370
