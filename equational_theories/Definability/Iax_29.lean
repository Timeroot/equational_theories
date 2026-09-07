import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation4478 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4478 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq492 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq496 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq492 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq492 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq492 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq492 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq531 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq496 (σ X1) (σ X0)
       grind)
    | exact superpose eq496 eq13
    | exact resolve eq13 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq531 X0 X1
       have i₂ := eq496 X1 X0
       grind)
    | exact superpose eq496 eq531
    | exact resolve eq531 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq531
  have eq1747 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq542 x y
       grind)
    | exact superpose eq542 eq14
    | (have r₁ := eq14
       have r₂ := eq542 x y
       grind)
    | exact resolve eq14 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq1778 : False := by grind
  exact eq1778

/-- `Equation4485`: `x ◇ (y ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4485 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4485 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X0 X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X1 X2) X1 X2
       have i₂ := eq8 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 X0)
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq8 X0 (M.op X1 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X1) = (M.op X1 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq60 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X2 X3 X4 (M.op X0 X0)
       have i₂ := eq8 X2 X0 X1
       grind)
    | (have i₁ := eq19 (M.op X1 X2) X1 X2 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X2 X4) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X0 X3) X2 X4
       have i₂ := eq19 X0 X3 (M.op X2 X2) X1
       grind)
    | (have i₁ := eq8 (M.op X0 X3) X2 X4
       have i₂ := eq19 X0 X1 (M.op X2 X2) X3
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq101 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq40 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq40 eq13
    | (have j1 := eq40 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X2 (τ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq40 (τ X1) X2 X0
       grind)
    | exact superpose eq40 eq16
    | (have j1 := eq40 (τ X1) X2 X2
       grind)
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq40 X1 (σ X0) X2
       grind)
    | exact superpose eq40 eq47
    | (have j1 := eq40 X1 X1 X2
       grind)
    | exact resolve eq47 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq121 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112
    | (have j0 := eq112 X0 X1 X2
       grind)
    | exact resolve eq112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq127 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op (M.op X4 X5) (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X4 X5 (M.op X0 X2) X3
       have i₂ := eq19 X0 X2 (M.op X0 X2) X1
       grind)
    | (have i₁ := eq21 X4 X5 (M.op X0 X2) X3
       have i₂ := eq19 X0 X1 (M.op X0 X2) X2
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 (M.op X2 X3) X1 X0 X4
       have i₂ := eq21 X2 X3 X1 X0
       grind)
    | (have i₁ := eq19 X0 X1 (M.op X2 X2) X3
       have i₂ := eq21 X0 X1 X2 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq19
    | exact resolve eq19 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 (M.op X1 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq105 X0 (M.op X1 X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq105
    | (have j0 := eq105 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq105 (M.op X0 (M.op X0 X0)) X0
       have r₂ := eq8 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq105 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 X1) ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq33 X1 X0 x X3
       grind)
    | exact superpose eq33 eq8
    | (have j1 := eq33 X1 X1 x X3
       grind)
    | exact resolve eq8 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq845 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X4 X5) X0) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq60 x x X4 X5 X0
       have i₂ := eq168 X0 X1 x x X4
       grind)
    | (have i₁ := eq60 X0 X1 x x (M.op X1 X1)
       have i₂ := eq168 (M.op (M.op X0 X1) x) X1 x x X4
       grind)
    | exact superpose eq168 eq60
    | exact resolve eq60 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq168
  have eq1162 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 X3 X4
       have i₂ := eq845 X2 X3 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X4 x) X1 X2
       have i₂ := eq845 (M.op X1 X1) X1 X4 x
       grind)
    | exact superpose eq845 eq8
    | exact resolve eq8 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2119 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 (σ X0)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X1 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq121
    | (have j0 := eq121 X0 (σ X0) X2
       grind)
    | exact resolve eq121 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2174 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq38 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq11 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2242 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq2246 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2174 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq2174 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq2174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2263 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2246 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq2246
    | (have j0 := eq2246 (τ X0) X1
       grind)
    | exact resolve eq2246 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2267 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2263 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2263
    | (have j0 := eq2263 X0 X1
       grind)
    | exact resolve eq2263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq2271 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2267 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2267
    | (have j0 := eq2267 X0 X1
       grind)
    | exact resolve eq2267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq2480 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2271 (τ X0) X1
       have i₂ := eq82 X0 X0
       grind)
    | exact superpose eq82 eq2271
    | (have j0 := eq2271 (τ X0) X1
       grind)
    | exact resolve eq2271 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq2271
  have eq3192 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq3341 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3192 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3192
    | (have j0 := eq3192 X0 X1
       grind)
    | exact resolve eq3192 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq4216 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X0
       have i₂ := eq3341 X1 X0
       grind)
    | exact superpose eq3341 eq105
    | (have j0 := eq105 X0 X0
       have j1 := eq3341 X1 X0
       grind)
    | (have r₁ := eq105 X1 X1
       have r₂ := eq3341 X0 X1
       grind)
    | exact resolve eq105 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq4261 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4216
  have eq7234 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2246 X0 X1
       have i₂ := eq4261 X0 X2
       grind)
    | exact superpose eq4261 eq2246
    | (have j0 := eq2246 X0 X1
       have j1 := eq4261 X0 X2
       grind)
    | exact resolve eq2246 eq4261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246 eq4261
  have eq7284 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq7234 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7234
  have eq8595 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2242 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq2242
    | (have j0 := eq2242 (τ X0)
       grind)
    | exact resolve eq2242 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8611 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8595 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8595
    | (have j0 := eq8595 X0
       grind)
    | exact resolve eq8595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8595
  have eq8618 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8611 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8611
    | (have j0 := eq8611 X0
       grind)
    | exact resolve eq8611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8611
  have eq9341 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq101 x y X0
       grind)
    | exact superpose eq101 eq14
    | (have j1 := eq101 X0 y X0
       grind)
    | exact resolve eq14 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq9462 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq9341 X0
       have j1 := eq7284 y X0 x
       grind)
    | (have r₁ := eq9341 X0
       have r₂ := eq7284 y x x
       grind)
    | exact resolve eq9341 eq7284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7284 eq9341
  have eq9497 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8618 (σ y)
       have i₂ := eq9462 (σ y)
       grind)
    | exact superpose eq9462 eq8618
    | (have j0 := eq8618 (σ y)
       grind)
    | (have r₁ := eq8618 (σ y)
       have r₂ := eq9462 (σ y)
       grind)
    | exact resolve eq8618 eq9462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9499 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2480 (σ y) X0
       have i₂ := eq9462 (σ y)
       grind)
    | exact superpose eq9462 eq2480
    | (have j0 := eq2480 (σ y) X0
       grind)
    | exact resolve eq2480 eq9462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9462
  have eq9525 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq9499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9499
  have eq9527 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq9497
  have eq9535 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9525 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq9525
    | exact resolve eq9525 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9525
  have eq9700 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8618 y
       have i₂ := eq9535 y
       grind)
    | exact superpose eq9535 eq8618
    | (have j0 := eq8618 y
       grind)
    | (have r₁ := eq8618 y
       have r₂ := eq9535 y
       grind)
    | exact resolve eq8618 eq9535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9707 : ∀ X0 X1 : G, (M.op X0 y) = X0 ∨ (M.op y X1) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq36 y X1 X0
       have i₂ := eq9535 X0
       grind)
    | exact superpose eq9535 eq36
    | (have j0 := eq36 y X1 x
       grind)
    | exact resolve eq36 eq9535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq9535
  have eq9727 : y = (M.op y y) := by grind
  clear eq9700
  have eq10045 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq845 X0 y X1 X2
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq845
    | exact resolve eq845 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10050 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq8
    | exact resolve eq8 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10071 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op y (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X1 y x y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq80
    | exact resolve eq80 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq10087 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 X1 y y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq845
    | exact resolve eq845 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq10089 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1162 X0 X1 X2 y y
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq1162
    | exact resolve eq1162 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10100 : ∀ X0 X2 : G, (M.op y y) = (M.op y (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq10071 X0 x X2
       have i₂ := eq10089 X0 x y
       grind)
    | exact superpose eq10089 eq10071
    | exact resolve eq10071 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10071
  have eq10119 : ∀ X0 X2 : G, y = (M.op y (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq10100 X0 X2
       have i₂ := eq9727
       grind)
    | exact superpose eq9727 eq10100
    | exact resolve eq10100 eq9727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9727 eq10100
  have eq19794 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1162 X0 X1 X2 (σ y) (σ y)
       have i₂ := eq9527
       grind)
    | exact superpose eq9527 eq1162
    | exact resolve eq1162 eq9527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq19796 : y = (M.op y (σ y)) := by
    first
    | (have i₁ := eq10119 (σ y) (σ y)
       have i₂ := eq9527
       grind)
    | exact superpose eq9527 eq10119
    | exact resolve eq10119 eq9527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19801 : ∀ X2 : G, (M.op (σ y) X2) = (M.op y X2) := by
    intro X2
    first
    | (have i₁ := eq19794 x x X2
       have i₂ := eq10089 x x X2
       grind)
    | exact superpose eq10089 eq19794
    | exact resolve eq19794 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19794
  have eq22032 : (σ y) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq9527
       have i₂ := eq19801 (σ y)
       grind)
    | exact superpose eq19801 eq9527
    | exact resolve eq9527 eq19801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9527 eq19801
  have eq22202 : y = (σ y) := by
    first
    | (have i₁ := eq22032
       have i₂ := eq19796
       grind)
    | exact superpose eq19796 eq22032
    | exact resolve eq22032 eq19796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19796 eq22032
  have eq23116 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq14
    | exact resolve eq14 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23123 : ∀ X0 : G, (k y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq13
    | exact resolve eq13 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23137 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq47 y X0
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq47
    | exact resolve eq47 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq23152 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq23116
       have i₂ := eq10050 (σ x)
       grind)
    | exact superpose eq10050 eq23116
    | exact resolve eq23116 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23116
  have eq30888 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k (σ (M.op (M.op X4 X5) (M.op X1 X3))) X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq103 (M.op (M.op X4 X5) (M.op X1 X3)) X0 X6
       have i₂ := eq127 X1 X2 X3 (τ X0) X4 X5
       grind)
    | exact superpose eq127 eq103
    | (have j0 := eq103 X0 X0 X6
       grind)
    | exact resolve eq103 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq127
  have eq30891 : ∀ X0 X1 X2 X3 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k (σ (M.op y (M.op X1 X3))) X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq30888 X0 X1 X2 X3 x x X6
       have i₂ := eq10089 x x (M.op X1 X3)
       grind)
    | exact superpose eq10089 eq30888
    | (have j0 := eq30888 X0 X1 X2 X3 x x X6
       grind)
    | exact resolve eq30888 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30888
  have eq31059 : ∀ X0 X1 X2 X3 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k (σ y) X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq30891 X0 X1 X2 X3 X6
       have i₂ := eq10119 X1 X3
       grind)
    | exact superpose eq10119 eq30891
    | (have j0 := eq30891 X0 X1 X2 X3 X6
       grind)
    | exact resolve eq30891 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30891
  have eq31218 : ∀ X0 X1 X2 X3 X6 : G, (σ (M.op (τ X0) (M.op (M.op X1 X2) (M.op X1 X3)))) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq31059 X0 X1 X2 X3 X6
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq31059
    | (have j0 := eq31059 X0 X1 X2 X3 X6
       grind)
    | exact resolve eq31059 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31059
  have eq31332 : ∀ X0 X1 X3 X6 : G, (σ (M.op (τ X0) (M.op y (M.op X1 X3)))) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X1 X3 X6
    first
    | (have i₁ := eq31218 X0 X1 x X3 X6
       have i₂ := eq10089 X1 x (M.op X1 X3)
       grind)
    | exact superpose eq10089 eq31218
    | (have j0 := eq31218 X0 X1 x X3 X6
       grind)
    | exact resolve eq31218 eq10089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31218
  have eq31341 : ∀ X0 X6 : G, (σ (M.op (τ X0) y)) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X6
    first
    | (have i₁ := eq31332 X0 x x X6
       have i₂ := eq10119 x x
       grind)
    | exact superpose eq10119 eq31332
    | (have j0 := eq31332 X0 x x X6
       grind)
    | exact resolve eq31332 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31332
  have eq31349 : ∀ X0 X6 : G, (σ (M.op y (τ X0))) = (k y X0) ∨ (k X6 (τ X0)) = X6 := by
    intro X0 X6
    first
    | (have i₁ := eq31341 X0 X6
       have i₂ := eq10050 (τ X0)
       grind)
    | exact superpose eq10050 eq31341
    | (have j0 := eq31341 X0 X6
       grind)
    | exact resolve eq31341 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31341
  have eq38564 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op y X0) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq485 X0 X1 X2
       have i₂ := eq10087 X0 X1
       grind)
    | exact superpose eq10087 eq485
    | (have j0 := eq485 X0 X1 X2
       grind)
    | exact resolve eq485 eq10087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41672 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2119 X0 X1 y
       have i₂ := eq23123 X0
       grind)
    | exact superpose eq23123 eq2119
    | (have j0 := eq2119 X0 X1 x
       grind)
    | exact resolve eq2119 eq23123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119
  have eq99839 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq9707 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9707
  have eq103998 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq99839 (M.op X0 X0)
       have i₂ := eq485 y X0 X1
       grind)
    | exact superpose eq485 eq99839
    | (have j0 := eq99839 (M.op X0 X0)
       have j1 := eq485 X0 X0 X1
       grind)
    | (have r₁ := eq99839 (M.op y y)
       have r₂ := eq485 y y x
       grind)
    | exact resolve eq99839 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq99839
  have eq104059 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) y) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq103998 X0 X1
       have j1 := eq38564 X0 X0 X1
       grind)
    | (have r₁ := eq103998 X1 X1
       have r₂ := eq38564 X1 X1 x
       grind)
    | (have r₁ := eq103998 y X1
       have r₂ := eq38564 y y x
       grind)
    | exact resolve eq103998 eq38564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38564 eq103998
  have eq104106 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104059 X0 X1
       have i₂ := eq8 y X0 X0
       grind)
    | exact superpose eq8 eq104059
    | (have j0 := eq104059 X0 X1
       grind)
    | exact resolve eq104059 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104059
  have eq104153 : ∀ X0 X1 : G, y = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104106 X0 X1
       have i₂ := eq10119 X0 X0
       grind)
    | exact superpose eq10119 eq104106
    | (have j0 := eq104106 X0 X1
       grind)
    | exact resolve eq104106 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10119 eq104106
  have eq121300 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23137 X0
       have i₂ := eq104153 X0 y
       grind)
    | exact superpose eq104153 eq23137
    | (have j1 := eq104153 X0 x
       grind)
    | exact resolve eq23137 eq104153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23137 eq104153
  have eq535751 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k y X1) = (σ (M.op y (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (τ X1)
       have i₂ := eq31349 X1 (τ X0)
       grind)
    | exact superpose eq31349 eq15
    | (have j1 := eq31349 X1 x
       grind)
    | exact resolve eq15 eq31349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq31349
  have eq535752 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k y X1) = (σ (M.op y (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq535751 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq535751
    | (have j0 := eq535751 X0 X1
       grind)
    | exact resolve eq535751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535751
  have eq535761 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k y X1) = (σ (M.op y (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq535752 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq535752
    | (have j0 := eq535752 X0 X1
       grind)
    | exact resolve eq535752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535752
  have eq541829 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op y (τ X0))) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq8618 X0
       have i₂ := eq535761 X0 X0
       grind)
    | exact superpose eq535761 eq8618
    | (have j0 := eq8618 X0
       have j1 := eq535761 X0 X0
       grind)
    | (have r₁ := eq8618 x
       have r₂ := eq535761 x x
       grind)
    | exact resolve eq8618 eq535761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535761
  have eq541871 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op y (τ X0))) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq541829 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541829
  have eq561204 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3341 y X0
       have i₂ := eq41672 X0 X1
       grind)
    | exact superpose eq41672 eq3341
    | (have j0 := eq3341 X0 X0
       have j1 := eq41672 X0 X1
       grind)
    | exact resolve eq3341 eq41672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341 eq41672
  have eq561262 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq561204 X0 X1
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq561204 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq561204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561204
  have eq563551 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq182 X0 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq563552 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq563551 x
       have i₂ := eq10087 x x
       grind)
    | exact superpose eq10087 eq563551
    | exact resolve eq563551 eq10087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10087 eq563551
  have eq563832 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (σ (M.op y (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y (τ X0))
       have i₂ := eq563552 (τ X0)
       grind)
    | exact superpose eq563552 eq16
    | exact resolve eq16 eq563552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563552
  have eq564652 : ∀ X0 : G, (k y X0) = (k (k y X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq563832 X0
       have i₂ := eq541871 X0
       grind)
    | exact superpose eq541871 eq563832
    | (have j1 := eq541871 X0
       grind)
    | exact resolve eq563832 eq541871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541871 eq563832
  have eq564801 : ∀ X0 : G, (k y X0) = (k (k y X0) X0) := by
    intro X0
    first
    | (have j0 := eq564652 X0
       have j1 := eq11 (k y X0) X0
       grind)
    | (have r₁ := eq564652 x
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq564652 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564652
  have eq564990 : ∀ X0 : G, (k y X0) = (M.op (k y X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (k y X0) X0
       have i₂ := eq564801 X0
       grind)
    | exact superpose eq564801 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq564801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564801
  have eq565271 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (k y X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10045 X1 (k y X0) X0
       have i₂ := eq564990 X0
       grind)
    | exact superpose eq564990 eq10045
    | (have j1 := eq564990 X0
       grind)
    | exact resolve eq10045 eq564990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10045
  have eq567484 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq564990 X0
       have i₂ := eq565271 X0 X0
       grind)
    | exact superpose eq565271 eq564990
    | (have j0 := eq564990 X0
       have j1 := eq565271 X0 x
       grind)
    | exact resolve eq564990 eq565271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564990 eq565271
  have eq567578 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq567484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567484
  have eq573957 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 y)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq121300 X0
       have i₂ := eq10050 X0
       grind)
    | (have i₁ := eq121300 y
       have i₂ := eq10050 y
       grind)
    | exact superpose eq10050 eq121300
    | (have j0 := eq121300 X0
       grind)
    | exact resolve eq121300 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121300
  have eq578633 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq561262 X0 X1
       have i₂ := eq10050 X0
       grind)
    | (have i₁ := eq561262 y X1
       have i₂ := eq10050 y
       grind)
    | exact superpose eq10050 eq561262
    | (have j0 := eq561262 X0 X1
       grind)
    | exact resolve eq561262 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561262
  have eq646029 : ∀ X0 : G, (M.op X0 y) = (σ (k y (τ X0))) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 y)
       have i₂ := eq573957 X0
       grind)
    | exact superpose eq573957 eq10
    | (have j1 := eq573957 X0
       grind)
    | exact resolve eq10 eq573957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573957
  have eq646069 : ∀ X0 : G, (M.op X0 y) = (k (σ y) X0) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq646029 X0
       have i₂ := eq16 X0 y
       grind)
    | exact superpose eq16 eq646029
    | (have j0 := eq646029 X0
       grind)
    | exact resolve eq646029 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq646029
  have eq646084 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq646069 X0
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq646069
    | (have j0 := eq646069 X0
       grind)
    | exact resolve eq646069 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646069
  have eq646275 : ∀ X0 : G, y = X0 ∨ (M.op X0 y) = (k y X0) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq567578 X0
       have i₂ := eq646084 X0
       grind)
    | exact superpose eq646084 eq567578
    | (have j0 := eq567578 X0
       have j1 := eq646084 X0
       grind)
    | exact resolve eq567578 eq646084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567578 eq646084
  have eq646325 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq646275 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646275
  have eq647844 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) y) ∨ (σ X0) = y := by
    intro X0
    first
    | (have i₁ := eq23123 X0
       have i₂ := eq646325 (σ X0)
       grind)
    | exact superpose eq646325 eq23123
    | (have j1 := eq646325 (σ X0)
       grind)
    | exact resolve eq23123 eq646325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23123 eq646325
  have eq648143 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ X0) = y := by
    intro X0
    first
    | (have i₁ := eq647844 X0
       have i₂ := eq10050 (σ X0)
       grind)
    | exact superpose eq10050 eq647844
    | (have j0 := eq647844 X0
       grind)
    | exact resolve eq647844 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10050 eq647844
  have eq701601 : ∀ X0 : G, (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq23152
       have i₂ := eq578633 x X0
       grind)
    | exact superpose eq578633 eq23152
    | (have j1 := eq578633 x X0
       grind)
    | (have r₁ := eq23152
       have r₂ := eq578633 x x
       grind)
    | exact resolve eq23152 eq578633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23152 eq578633
  have eq701615 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq701601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701601
  have eq707298 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2242 x
       have i₂ := eq701615 x
       grind)
    | exact superpose eq701615 eq2242
    | (have j0 := eq2242 x
       grind)
    | exact resolve eq2242 eq701615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq707302 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (k X0 (τ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2480 x X0
       have i₂ := eq701615 x
       grind)
    | exact superpose eq701615 eq2480
    | (have j0 := eq2480 x X0
       grind)
    | exact resolve eq2480 eq701615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq707303 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8618 x
       have i₂ := eq701615 x
       grind)
    | exact superpose eq701615 eq8618
    | (have j0 := eq8618 x
       grind)
    | (have r₁ := eq8618 x
       have r₂ := eq701615 x
       grind)
    | exact resolve eq8618 eq701615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8618 eq701615
  have eq707608 : x = (M.op x x) := by grind
  clear eq707303
  have eq707609 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq707302 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707302
  have eq707613 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq707298
  have eq708628 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10089 x x X0
       have i₂ := eq707608
       grind)
    | exact superpose eq707608 eq10089
    | exact resolve eq10089 eq707608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10089
  have eq709623 : (σ y) = (M.op y (σ (τ x))) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq648143 (τ x)
       have i₂ := eq707609 y
       grind)
    | exact superpose eq707609 eq648143
    | (have j0 := eq648143 (τ x)
       grind)
    | exact resolve eq648143 eq707609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648143 eq707609
  have eq709636 : (σ y) = (M.op x (σ (τ x))) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709623
       have i₂ := eq708628 (σ (τ x))
       grind)
    | exact superpose eq708628 eq709623
    | exact resolve eq709623 eq708628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708628 eq709623
  have eq709812 : (σ y) = (M.op x x) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709636
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq709636
    | exact resolve eq709636 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709636
  have eq709877 : x = (σ y) ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709812
       have i₂ := eq707608
       grind)
    | exact superpose eq707608 eq709812
    | exact resolve eq709812 eq707608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709812
  have eq709901 : x = y ∨ y = (σ (τ x)) := by
    first
    | (have i₁ := eq709877
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq709877
    | exact resolve eq709877 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22202 eq709877
  have eq709909 : x = y ∨ x = y := by
    first
    | (have i₁ := eq709901
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq709901
    | exact resolve eq709901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709901
  have eq709910 : x = y := by grind
  clear eq709909
  have eq709913 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq709910
       grind)
    | exact superpose eq709910 eq14
    | exact resolve eq14 eq709910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709910
  have eq710329 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq709913
       have i₂ := eq707608
       grind)
    | exact superpose eq707608 eq709913
    | exact resolve eq709913 eq707608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707608 eq709913
  have eq710336 : False := by grind
  exact eq710336

/-- `Equation4497`: `x ◇ (y ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyy_pxy_Equation4497 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4497 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4497.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq24 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 (M.op x x) X1 x
       have i₂ := eq8 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | (have i₁ := eq8 (M.op X1 X1) X1 X2
       have i₂ := eq8 (M.op X2 X2) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    grind
  have eq100 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X2 X3 (M.op X1 X1)
       have i₂ := eq8 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq24 X2 X3 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq24
    | exact resolve eq24 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X2 X3 (M.op X1 X1)
       have i₂ := eq8 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq28 X2 X3 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq28
    | exact resolve eq28 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq65 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq65
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq65 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq562 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1691 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq562 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1946 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1691 (σ X0)
       grind)
    | exact superpose eq1691 eq13
    | exact resolve eq13 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1948 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0 X0
       have i₂ := eq1691 (τ X0)
       grind)
    | exact superpose eq1691 eq49
    | exact resolve eq49 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1955 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1948 X0
       have i₂ := eq1691 X0
       grind)
    | exact superpose eq1691 eq1948
    | exact resolve eq1948 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq1957 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1946 X0
       have i₂ := eq1691 X0
       grind)
    | exact superpose eq1691 eq1946
    | exact resolve eq1946 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691 eq1946
  have eq2218 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (τ X0) X2
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq8
    | exact resolve eq8 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2226 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (τ X0)
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq24
    | exact resolve eq24 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2231 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X2 (τ X0)
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq28
    | exact resolve eq28 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2337 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (σ X0)
       have i₂ := eq1957 X0
       grind)
    | exact superpose eq1957 eq24
    | exact resolve eq24 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2342 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X2 (σ X0)
       have i₂ := eq1957 X0
       grind)
    | exact superpose eq1957 eq28
    | exact resolve eq28 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2414 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq14
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq14 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq2574 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2414
       have i₂ := eq1957 x
       grind)
    | exact superpose eq1957 eq2414
    | exact resolve eq2414 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957 eq2414
  have eq2728 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op X2 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2218 (τ X0) X2 X1
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq2218
    | exact resolve eq2218 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218
  have eq3631 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (τ (τ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2226 (τ X0) X1 X2
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq2226
    | exact resolve eq2226 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226
  have eq4190 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2231 (τ X0) X1 X2
       have i₂ := eq1955 X0
       grind)
    | exact superpose eq1955 eq2231
    | exact resolve eq2231 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955 eq2231
  have eq23592 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2574
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq2574
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq2574 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq23598 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq23592
  have eq23605 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq23598
       grind)
    | exact superpose eq23598 eq9
    | exact resolve eq9 eq23598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23598
  have eq23641 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23605
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq23605
    | exact resolve eq23605 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23605
  have eq23642 : y = (M.op x x) := by grind
  clear eq23641
  have eq24113 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x X1
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq8
    | exact resolve eq8 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24151 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X2 X2) y) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X2 x X0 X1
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq100
    | exact resolve eq100 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq24155 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X1) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq156 X1 x X0 X2
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq156
    | exact resolve eq156 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq24157 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 y) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1 x
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq191
    | (have j0 := eq191 X0 X1 x
       grind)
    | exact resolve eq191 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq24192 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2337 x X0 X1
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq2337
    | exact resolve eq2337 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337
  have eq24193 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2342 x X0 X1
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq2342
    | exact resolve eq2342 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq24201 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (τ (τ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2728 x X0 X1
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq2728
    | exact resolve eq2728 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24248 : ∀ X0 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op y (τ (τ y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq24155 X0 x X2
       have i₂ := eq24201 x y
       grind)
    | exact superpose eq24201 eq24155
    | exact resolve eq24155 eq24201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24155
  have eq24251 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (τ (τ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24151 X0 X1 x
       have i₂ := eq24201 x y
       grind)
    | exact superpose eq24201 eq24151
    | exact resolve eq24151 eq24201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24151
  have eq24298 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op y (τ (τ y)))) := by
    intro X0
    first
    | (have i₁ := eq24248 X0 x
       have i₂ := eq24193 X0 x
       grind)
    | exact superpose eq24193 eq24248
    | exact resolve eq24248 eq24193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24193 eq24248
  have eq24301 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (M.op y (τ (τ y))) X1) := by
    intro X1
    first
    | (have i₁ := eq24251 x X1
       have i₂ := eq24192 x X1
       grind)
    | exact superpose eq24192 eq24251
    | exact resolve eq24251 eq24192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24192 eq24251
  have eq75223 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq24113 X0 x
       have i₂ := eq23642
       grind)
    | exact superpose eq23642 eq24113
    | exact resolve eq24113 eq23642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23642
  have eq75324 : ∀ X0 X2 : G, (M.op X0 (τ (τ (M.op X2 X2)))) = (M.op X0 y) := by
    intro X0 X2
    first
    | (have i₁ := eq2728 X2 x X0
       have i₂ := eq24113 X0 x
       grind)
    | exact superpose eq24113 eq2728
    | exact resolve eq2728 eq24113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728
  have eq75325 : ∀ X0 X2 : G, (M.op (τ (τ (M.op X2 X2))) X0) = (M.op X0 y) := by
    intro X0 X2
    first
    | (have i₁ := eq3631 X2 x X0
       have i₂ := eq24113 X0 x
       grind)
    | exact superpose eq24113 eq3631
    | exact resolve eq3631 eq24113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75498 : ∀ X0 X1 X2 : G, (M.op (τ (τ (M.op X2 X2))) X1) = (M.op (M.op (M.op X0 X0) y) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3631 X2 (M.op X0 X0) X1
       have i₂ := eq24113 (M.op X0 X0) X0
       grind)
    | exact superpose eq24113 eq3631
    | exact resolve eq3631 eq24113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq75502 : ∀ X0 X1 X2 : G, (M.op X1 (τ (τ (M.op X2 X2)))) = (M.op X1 (M.op (M.op X0 X0) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4190 X2 X1 (M.op X0 X0)
       have i₂ := eq24113 (M.op X0 X0) X0
       grind)
    | exact superpose eq24113 eq4190
    | exact resolve eq4190 eq24113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4190 eq24113
  have eq75611 : ∀ X1 X2 : G, (M.op X1 (τ (τ (M.op X2 X2)))) = (M.op X1 (M.op y (τ (τ y)))) := by
    intro X1 X2
    first
    | (have i₁ := eq75502 x X1 X2
       have i₂ := eq24201 x y
       grind)
    | exact superpose eq24201 eq75502
    | exact resolve eq75502 eq24201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75502
  have eq75615 : ∀ X1 X2 : G, (M.op (τ (τ (M.op X2 X2))) X1) = (M.op (M.op y (τ (τ y))) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq75498 x X1 X2
       have i₂ := eq24201 x y
       grind)
    | exact superpose eq24201 eq75498
    | exact resolve eq75498 eq24201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24201 eq75498
  have eq76012 : ∀ X1 X2 : G, (M.op X1 (τ (τ (M.op X2 X2)))) = (M.op X1 (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq75611 X1 X2
       have i₂ := eq24298 X1
       grind)
    | exact superpose eq24298 eq75611
    | exact resolve eq75611 eq24298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24298 eq75611
  have eq76016 : ∀ X1 X2 : G, (M.op (τ (τ (M.op X2 X2))) X1) = (M.op (σ y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq75615 X1 X2
       have i₂ := eq24301 X1
       grind)
    | exact superpose eq24301 eq75615
    | exact resolve eq75615 eq24301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24301 eq75615
  have eq76391 : ∀ X1 : G, (M.op X1 y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq76012 X1 x
       have i₂ := eq75324 X1 x
       grind)
    | exact superpose eq75324 eq76012
    | exact resolve eq76012 eq75324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75324 eq76012
  have eq76392 : ∀ X1 : G, (M.op X1 y) = (M.op (σ y) X1) := by
    intro X1
    first
    | (have i₁ := eq76016 X1 x
       have i₂ := eq75325 X1 x
       grind)
    | exact superpose eq75325 eq76016
    | exact resolve eq76016 eq75325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75325 eq76016
  have eq105961 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq76391 (σ x)
       grind)
    | exact superpose eq76391 eq14
    | exact resolve eq14 eq76391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76391
  have eq106012 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq105961
       have i₂ := eq75223 (σ x)
       grind)
    | exact superpose eq75223 eq105961
    | exact resolve eq105961 eq75223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105961
  have eq1963156 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 y) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq24157 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24157
  have eq2049760 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1963156 (σ y) x
       have i₂ := eq76392 x
       grind)
    | exact superpose eq76392 eq1963156
    | (have r₁ := eq1963156 (σ y) x
       have r₂ := eq76392 x
       grind)
    | exact resolve eq1963156 eq76392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76392
  have eq2049788 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq1963156 y X0
       have i₂ := eq75223 X0
       grind)
    | (have i₁ := eq1963156 X0 y
       have i₂ := eq75223 X0
       grind)
    | exact superpose eq75223 eq1963156
    | (have r₁ := eq1963156 y X0
       have r₂ := eq75223 X0
       grind)
    | (have r₁ := eq1963156 y y
       have r₂ := eq75223 y
       grind)
    | exact resolve eq1963156 eq75223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963156
  have eq2049798 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq2049788 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049788
  have eq2049812 : ∀ X0 : G, (M.op X0 y) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq2049760 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049760
  have eq2056382 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq2049812 (σ X0)
       grind)
    | exact superpose eq2049812 eq13
    | exact resolve eq13 eq2049812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049812
  have eq2056545 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2056382 X0
       have i₂ := eq75223 (σ X0)
       grind)
    | exact superpose eq75223 eq2056382
    | exact resolve eq2056382 eq75223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75223 eq2056382
  have eq2056641 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq2056545 X0
       have i₂ := eq2049798 X0
       grind)
    | exact superpose eq2049798 eq2056545
    | exact resolve eq2056545 eq2049798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049798 eq2056545
  have eq2107199 : (M.op y (σ x)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq106012
       have i₂ := eq2056641 x
       grind)
    | exact superpose eq2056641 eq106012
    | (have r₁ := eq106012
       have r₂ := eq2056641 x
       grind)
    | exact resolve eq106012 eq2056641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106012 eq2056641
  have eq2107210 : False := by grind
  exact eq2107210

/-- `Equation4497`: `x ◇ (y ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4497 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4497 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4497.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X2) X0) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) X3
       have i₂ := eq8 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X0 X0) X3
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 (M.op x x) X1 x
       have i₂ := eq8 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X1 X1)
       have i₂ := eq8 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq8 X2 X3 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | (have i₁ := eq8 (M.op X1 X1) X1 X2
       have i₂ := eq8 (M.op X2 X2) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X2 X2) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X0) X1 X3
       have i₂ := eq8 (M.op X3 X3) X0 X2
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq38 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X2)) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq86 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32
    | exact resolve eq32 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq32
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq33 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq158 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq40
    | exact resolve eq40 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq187 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq173 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq173
    | exact resolve eq173 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq275 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ X1 ∨ (k X1 (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165 X1 (M.op X2 X2)
       have i₂ := eq8 X1 X2 X0
       grind)
    | (have i₁ := eq165 (M.op X2 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq165
    | (have j0 := eq165 X1 (M.op X2 X2)
       grind)
    | (have r₁ := eq165 (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)
       have r₂ := eq8 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact resolve eq165 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) X4) = (M.op X4 (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq19 (M.op X2 X2) X5 X4 X3
       have i₂ := eq23 X0 X1 (M.op X2 X2) X2
       grind)
    | (have i₁ := eq19 (M.op (M.op X0 X0) (M.op X1 X1)) X5 X4 X3
       have i₂ := eq23 X0 X1 (M.op (M.op X0 X0) (M.op X1 X1)) X2
       grind)
    | exact superpose eq23 eq19
    | exact resolve eq19 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq23
  have eq525 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X2 X2) (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2
    grind
  clear eq25
  have eq540 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq187 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq187
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq187 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op X2 X0) ∨ (k X4 X1) = (M.op X4 X1) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq38 X1 X2 X3 X4
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq38 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq38
    | (have j0 := eq38 X1 X1 X2 X4
       have j1 := eq12 X4 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1151 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq43 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq43
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq14
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1199 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq9
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq187
    | (have j1 := eq43 X1 X0
       grind)
    | exact resolve eq187 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1230 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ X0)) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X1 X2 (σ X3)
       have i₂ := eq43 X3 X0
       grind)
    | exact superpose eq43 eq24
    | (have j1 := eq43 X3 X0
       grind)
    | exact resolve eq24 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1246 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1250 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1215 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1215
    | (have j0 := eq1215 X0 X1
       grind)
    | exact resolve eq1215 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq2383 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1246 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1246
    | (have j0 := eq1246 (τ X0)
       grind)
    | exact resolve eq1246 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2386 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2383 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2383
    | (have j0 := eq2383 X0
       grind)
    | exact resolve eq2383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2389 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2386 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2386
    | (have j0 := eq2386 X0
       grind)
    | exact resolve eq2386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386
  have eq2436 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2540 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq10
    | (have j1 := eq46 X0 X1
       grind)
    | exact resolve eq10 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq2568 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2436 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2436
    | (have j0 := eq2436 X0 X1
       grind)
    | exact resolve eq2436 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436
  have eq2593 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2389 (τ X0)
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq2389
    | (have j0 := eq2389 (τ X0)
       grind)
    | exact resolve eq2389 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2389
  have eq2942 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq4130 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq14
    | (have j1 := eq158 x y
       grind)
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4136 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq158 X0 X0
       grind)
    | exact superpose eq158 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq158 X0 X0
       grind)
    | exact resolve eq12 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4434 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1167
       have i₂ := eq2942 y x
       grind)
    | exact superpose eq2942 eq1167
    | (have j1 := eq2942 y x
       grind)
    | (have r₁ := eq1167
       have r₂ := eq2942 y x
       grind)
    | exact resolve eq1167 eq2942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2942
  have eq4435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1167
       have i₂ := eq2568 y x
       grind)
    | exact superpose eq2568 eq1167
    | (have j1 := eq2568 (σ y) (σ x)
       grind)
    | (have r₁ := eq1167
       have r₂ := eq2568 y x
       grind)
    | exact resolve eq1167 eq2568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4436 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq4435
  have eq4437 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq4434
  have eq4447 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq4436
       grind)
    | exact superpose eq4436 eq187
    | exact resolve eq187 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4450 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (σ x) X1
       have i₂ := eq4436
       grind)
    | exact superpose eq4436 eq8
    | exact resolve eq8 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4461 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 (σ x)
       have i₂ := eq4436
       grind)
    | exact superpose eq4436 eq24
    | exact resolve eq24 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4494 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4447
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4447
    | exact resolve eq4447 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4447
  have eq4584 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2568 y x
       have i₂ := eq4494
       grind)
    | exact superpose eq4494 eq2568
    | (have j0 := eq2568 y x
       grind)
    | exact resolve eq2568 eq4494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4494
  have eq4585 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq4584
  have eq4600 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1199 X0 X1
       have i₂ := eq158 X0 X0
       grind)
    | exact superpose eq158 eq1199
    | (have j0 := eq1199 X0 X1
       have j1 := eq158 X0 X1
       grind)
    | exact resolve eq1199 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq4638 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1199 x x
       have i₂ := eq4436
       grind)
    | exact superpose eq4436 eq1199
    | exact resolve eq1199 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq4667 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4638
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4638
    | exact resolve eq4638 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4638
  have eq4674 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4600 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq4600
    | (have j0 := eq4600 X0 X1
       grind)
    | exact resolve eq4600 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600
  have eq6466 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq4437
       grind)
    | exact superpose eq4437 eq187
    | exact resolve eq187 eq4437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq4437
  have eq6529 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq6466
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6466
    | exact resolve eq6466 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6466
  have eq6530 : x = (k x y) := by grind
  clear eq6529
  have eq9107 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq145 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq145
    | (have j0 := eq145 X1 (σ X0)
       grind)
    | exact resolve eq145 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9127 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1246 (τ X0)
       have i₂ := eq145 (τ X0) X0
       grind)
    | exact superpose eq145 eq1246
    | (have j0 := eq1246 (τ X0)
       have j1 := eq145 (τ X0) X0
       grind)
    | exact resolve eq1246 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq9169 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9127 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9127
    | (have j0 := eq9127 X0
       grind)
    | exact resolve eq9127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9127
  have eq9180 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9107 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq9107
    | (have j0 := eq9107 X0 X1
       grind)
    | exact resolve eq9107 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9107
  have eq9193 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9169 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9169
    | (have j0 := eq9169 X0
       grind)
    | exact resolve eq9169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9169
  have eq9209 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq9193 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9193
    | (have j0 := eq9193 X0
       grind)
    | exact resolve eq9193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9193
  have eq9222 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9209 X0
       have j1 := eq165 X0 X0
       grind)
    | (have r₁ := eq9209 x
       have r₂ := eq165 x x
       grind)
    | exact resolve eq9209 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9209
  have eq9914 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9222 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq9222
    | (have j0 := eq9222 (σ X0)
       grind)
    | exact resolve eq9222 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9222
  have eq9939 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9914 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq9914
    | (have j0 := eq9914 X0
       grind)
    | exact resolve eq9914 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9914
  have eq19688 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq540 (σ X1) X0
       grind)
    | exact superpose eq540 eq32
    | (have j1 := eq540 (σ X1) X0
       grind)
    | exact resolve eq32 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq19718 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19688 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq19688
    | (have j0 := eq19688 X0 X1
       grind)
    | exact resolve eq19688 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19688
  have eq19754 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19718 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq19718
    | (have j0 := eq19718 X0 X1
       grind)
    | exact resolve eq19718 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19718
  have eq25014 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2593 (σ X0)
       have i₂ := eq540 (σ X0) X0
       grind)
    | exact superpose eq540 eq2593
    | (have j0 := eq2593 (σ X0)
       have j1 := eq540 (σ X0) X0
       grind)
    | exact resolve eq2593 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq25038 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq25014 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq25014
    | (have j0 := eq25014 X0
       grind)
    | exact resolve eq25014 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25014
  have eq25046 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq25038 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq25038
    | (have j0 := eq25038 X0
       grind)
    | exact resolve eq25038 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25038
  have eq25048 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq25046 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq25046
    | (have j0 := eq25046 X0
       grind)
    | exact resolve eq25046 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25046
  have eq25050 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25048 X0
       have j1 := eq165 X0 X0
       grind)
    | (have r₁ := eq25048 x
       have r₂ := eq165 x x
       grind)
    | exact resolve eq25048 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25048
  have eq36601 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq4667
       grind)
    | exact superpose eq4667 eq9
    | exact resolve eq9 eq4667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4667
  have eq36653 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36601
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq36601
    | exact resolve eq36601 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36601
  have eq37154 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x x
       have i₂ := eq36653
       grind)
    | exact superpose eq36653 eq40
    | exact resolve eq40 eq36653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36653
  have eq37162 : y = (M.op x x) ∨ x = y := by grind
  clear eq37154
  have eq38377 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x X1
       have i₂ := eq37162
       grind)
    | exact superpose eq37162 eq8
    | exact resolve eq8 eq37162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38383 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 x
       have i₂ := eq37162
       grind)
    | exact superpose eq37162 eq20
    | exact resolve eq20 eq37162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38387 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x
       have i₂ := eq37162
       grind)
    | exact superpose eq37162 eq24
    | exact resolve eq24 eq37162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39853 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38377 X0 x
       have i₂ := eq37162
       grind)
    | exact superpose eq37162 eq38377
    | exact resolve eq38377 eq37162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38377
  have eq40270 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq39853 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39853
  have eq45592 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op y (M.op X0 X0))) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq38387 X1 (M.op X0 X0)
       have i₂ := eq38383 X0 (M.op X0 X0)
       grind)
    | exact superpose eq38383 eq38387
    | exact resolve eq38387 eq38383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38383 eq38387
  have eq46072 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op y (M.op X0 X0))) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq45592 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45592
  have eq50825 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq1230 y X0 X1 x
       grind)
    | exact superpose eq1230 eq14
    | (have j1 := eq1230 y X0 X1 x
       grind)
    | exact resolve eq14 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq51044 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq50825 X0 X1
       have i₂ := eq6530
       grind)
    | exact superpose eq6530 eq50825
    | (have j0 := eq50825 X0 X1
       grind)
    | exact resolve eq50825 eq6530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50825
  have eq53017 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X2) = (M.op X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq703 X1 X1 X2 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq53018 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq53017 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53017
  have eq55157 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1167
       have i₂ := eq53018 x y X0
       grind)
    | exact superpose eq53018 eq1167
    | (have j1 := eq53018 X0 y X0
       grind)
    | exact resolve eq1167 eq53018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq53018
  have eq55164 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq55157 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55157
  have eq91660 : ∀ X0 : G, x ≠ (τ (σ y)) ∨ x = (k x x) ∨ (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq25050 x
       have i₂ := eq55164 X0
       grind)
    | exact superpose eq55164 eq25050
    | (have j0 := eq25050 x
       have j1 := eq55164 X0
       grind)
    | exact resolve eq25050 eq55164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25050 eq55164
  have eq92025 : ∀ X0 : G, x ≠ y ∨ x = (k x x) ∨ (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq91660 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq91660
    | (have j0 := eq91660 X0
       grind)
    | exact resolve eq91660 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91660
  have eq92028 : ∀ X0 : G, x = (k x x) ∨ (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq92025 X0
       have j1 := eq40270 X0
       grind)
    | (have r₁ := eq92025 X0
       have r₂ := eq40270 X0
       grind)
    | exact resolve eq92025 eq40270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40270 eq92025
  have eq103467 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19754 x x
       have i₂ := eq4436
       grind)
    | exact superpose eq4436 eq19754
    | (have j0 := eq19754 x x
       grind)
    | exact resolve eq19754 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19754
  have eq103548 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103467
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq103467
    | exact resolve eq103467 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103467
  have eq125599 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq103548
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq103548
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq103548 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125670 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq125599
  have eq126473 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x X1
       have i₂ := eq125670
       grind)
    | exact superpose eq125670 eq8
    | exact resolve eq8 eq125670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126752 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq165 x x
       have i₂ := eq125670
       grind)
    | exact superpose eq125670 eq165
    | (have j0 := eq165 x x
       grind)
    | (have r₁ := eq165 x x
       have r₂ := eq125670
       grind)
    | exact resolve eq165 eq125670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125670
  have eq126754 : x ≠ y ∨ x = (k x x) := by
    first
    | (have j1 := eq165 x x
       grind)
    | (have r₁ := eq126752
       have r₂ := eq165 x x
       grind)
    | exact resolve eq126752 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126752
  have eq130733 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y y) ∨ x = (k x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq92028 (M.op X0 X0)
       have i₂ := eq126473 y X0
       grind)
    | exact superpose eq126473 eq92028
    | exact resolve eq92028 eq126473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92028 eq126473
  have eq130746 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y y) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq130733 X0
       have j1 := eq165 x x
       grind)
    | (have r₁ := eq130733 X0
       have r₂ := eq165 x x
       grind)
    | exact resolve eq130733 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq130733
  have eq150833 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) ∨ x = y ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq46072 x X0
       have i₂ := eq130746 x
       grind)
    | exact superpose eq130746 eq46072
    | exact resolve eq46072 eq130746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46072
  have eq150902 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op y y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq379 x x (M.op x x) X0 y (M.op (M.op x x) (M.op x x))
       have i₂ := eq130746 (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) (M.op x x)))
       grind)
    | exact superpose eq130746 eq379
    | exact resolve eq379 eq130746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq130746
  have eq150918 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq150833 X0
       grind)
    | (have r₁ := eq150833 X0
       have r₂ := eq126754
       grind)
    | exact resolve eq150833 eq126754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150833
  have eq157721 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) ≠ (M.op y y) ∨ (M.op y y) = (k (M.op y y) (M.op X1 X1)) ∨ x = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 (M.op y y) X1
       have i₂ := eq150918 (M.op X0 X0)
       grind)
    | exact superpose eq150918 eq275
    | (have j0 := eq275 X0 (M.op y y) X1
       grind)
    | exact resolve eq275 eq150918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq150918
  have eq157845 : ∀ X1 : G, (M.op y y) = (k (M.op y y) (M.op X1 X1)) ∨ x = (k x x) := by
    intro X1
    first
    | (have j0 := eq157721 x X1
       grind)
    | (have r₁ := eq157721 x X1
       have r₂ := eq150902 x
       grind)
    | exact resolve eq157721 eq150902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150902 eq157721
  have eq264628 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ x) x
       have i₂ := eq4436
       grind)
    | exact superpose eq4436 eq89
    | exact resolve eq89 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq264807 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq264628
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq264628
    | exact resolve eq264628 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264628
  have eq264821 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq264807
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq264807
    | exact resolve eq264807 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264807
  have eq272301 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9180 x x
       have i₂ := eq264821
       grind)
    | exact superpose eq264821 eq9180
    | exact resolve eq9180 eq264821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9180 eq264821
  have eq272308 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq272301
  have eq308032 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq2540 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq308033 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq308032 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq308032
    | (have j0 := eq308032 X0
       grind)
    | exact resolve eq308032 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308032
  have eq309604 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq308033 X0
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq308033
    | (have j0 := eq308033 X0
       have j1 := eq40 X0 X0
       grind)
    | (have r₁ := eq308033 X0
       have r₂ := eq40 X0 X0
       grind)
    | exact resolve eq308033 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq309613 : x ≠ y ∨ x = (σ (M.op (τ x) (τ x))) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq308033 x
       have i₂ := eq103548
       grind)
    | exact superpose eq103548 eq308033
    | (have j0 := eq308033 x
       grind)
    | (have r₁ := eq308033 x
       have r₂ := eq103548
       grind)
    | exact resolve eq308033 eq103548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103548
  have eq309622 : x ≠ y ∨ x = (σ (M.op (τ x) (τ x))) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq308033 x
       grind)
    | (have r₁ := eq309613
       have r₂ := eq308033 x
       grind)
    | exact resolve eq309613 eq308033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309613
  have eq309624 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq309604 X0
       have j1 := eq308033 X0
       grind)
    | (have r₁ := eq309604 X0
       have r₂ := eq308033 X0
       grind)
    | exact resolve eq309604 eq308033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309604
  have eq309625 : x = (σ (M.op (τ x) (τ x))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq309622
       have r₂ := eq37162
       grind)
    | exact resolve eq309622 eq37162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37162 eq309622
  have eq311880 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq309624 (σ x)
       have i₂ := eq4436
       grind)
    | exact superpose eq4436 eq309624
    | (have j0 := eq309624 (σ x)
       grind)
    | exact resolve eq309624 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4436 eq309624
  have eq311896 : (σ x) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq311880
       have r₂ := eq272308
       grind)
    | exact resolve eq311880 eq272308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272308 eq311880
  have eq311902 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq311896
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq311896
    | exact resolve eq311896 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311896
  have eq316923 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9939 x
       have i₂ := eq311902
       grind)
    | exact superpose eq311902 eq9939
    | (have j0 := eq9939 x
       grind)
    | (have r₁ := eq9939 x
       have r₂ := eq311902
       grind)
    | exact resolve eq9939 eq311902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9939 eq311902
  have eq316947 : (σ x) = (σ (k x x)) ∨ y = (M.op x x) := by grind
  clear eq316923
  have eq319773 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1246 x
       have i₂ := eq316947
       grind)
    | exact superpose eq316947 eq1246
    | (have j0 := eq1246 x
       grind)
    | (have r₁ := eq1246 x
       have r₂ := eq316947
       grind)
    | exact resolve eq1246 eq316947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319776 : (k x x) = (τ (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq316947
       grind)
    | exact superpose eq316947 eq9
    | exact resolve eq9 eq316947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316947
  have eq319799 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq319773
  have eq319821 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq319776
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq319776
    | exact resolve eq319776 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319776
  have eq321743 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2593 x
       have i₂ := eq319821
       grind)
    | exact superpose eq319821 eq2593
    | (have j0 := eq2593 x
       grind)
    | exact resolve eq2593 eq319821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2593 eq319821
  have eq321762 : (τ x) = (M.op (τ x) (τ x)) ∨ y = (M.op x x) := by grind
  clear eq321743
  have eq324633 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq4450 X0 (σ x)
       have i₂ := eq319799
       grind)
    | exact superpose eq319799 eq4450
    | exact resolve eq4450 eq319799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4450
  have eq324636 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq4461 X0 (σ x)
       have i₂ := eq319799
       grind)
    | exact superpose eq319799 eq4461
    | exact resolve eq4461 eq319799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324696 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq324636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324636
  have eq324699 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq324633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324633
  have eq325552 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (τ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq4461 X0 (τ x)
       have i₂ := eq321762
       grind)
    | exact superpose eq321762 eq4461
    | exact resolve eq4461 eq321762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4461
  have eq325612 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (τ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq325552 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325552
  have eq342833 : (τ x) = (M.op (τ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq321762
       have i₂ := eq325612 (τ x)
       grind)
    | exact superpose eq325612 eq321762
    | exact resolve eq321762 eq325612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321762
  have eq342834 : x = (σ (M.op (τ x) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq309625
       have i₂ := eq325612 (τ x)
       grind)
    | exact superpose eq325612 eq309625
    | exact resolve eq309625 eq325612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309625
  have eq342837 : x = (σ (M.op (τ x) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq342834
  have eq342838 : (τ x) = (M.op (τ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq342833
  have eq344772 : x = (σ (M.op (σ x) (τ x))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq342837
       have i₂ := eq324699 (τ x)
       grind)
    | exact superpose eq324699 eq342837
    | exact resolve eq342837 eq324699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342837
  have eq344794 : x = (σ (M.op (σ x) (τ x))) ∨ y = (M.op x x) := by grind
  clear eq344772
  have eq346363 : (τ x) = (M.op (σ x) (τ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq324699 (τ x)
       have i₂ := eq342838
       grind)
    | exact superpose eq342838 eq324699
    | exact resolve eq324699 eq342838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324699 eq342838
  have eq346374 : (τ x) = (M.op (σ x) (τ x)) ∨ y = (M.op x x) := by grind
  clear eq346363
  have eq354334 : x = (σ (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq344794
       have i₂ := eq325612 (σ x)
       grind)
    | exact superpose eq325612 eq344794
    | exact resolve eq344794 eq325612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344794
  have eq354352 : x = (σ (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq354334
  have eq367087 : (M.op (σ x) (σ y)) = (τ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq325612 (σ x)
       have i₂ := eq346374
       grind)
    | exact superpose eq346374 eq325612
    | exact resolve eq325612 eq346374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325612 eq346374
  have eq367092 : (M.op (σ x) (σ y)) = (τ x) ∨ y = (M.op x x) := by grind
  clear eq367087
  have eq371423 : x = (σ (M.op (σ x) (σ x))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq354352
       have i₂ := eq324696 (σ x)
       grind)
    | exact superpose eq324696 eq354352
    | exact resolve eq354352 eq324696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324696 eq354352
  have eq371431 : x = (σ (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by grind
  clear eq371423
  have eq379097 : (σ (M.op x y)) ≠ (τ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq367092
       grind)
    | exact superpose eq367092 eq14
    | exact resolve eq14 eq367092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367092
  have eq382417 : (σ x) ≠ (τ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq379097
       have i₂ := eq4585
       grind)
    | exact superpose eq4585 eq379097
    | exact resolve eq379097 eq4585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4585 eq379097
  have eq382418 : (σ x) ≠ (τ x) ∨ y = (M.op x x) := by grind
  clear eq382417
  have eq391593 : x = (σ (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq371431
       have i₂ := eq319799
       grind)
    | exact superpose eq319799 eq371431
    | exact resolve eq371431 eq319799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319799 eq371431
  have eq391618 : x = (σ (σ x)) ∨ y = (M.op x x) := by grind
  clear eq391593
  have eq397551 : (σ x) = (τ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (σ x)
       have i₂ := eq391618
       grind)
    | exact superpose eq391618 eq9
    | exact resolve eq9 eq391618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391618
  have eq397586 : y = (M.op x x) := by
    first
    | (have r₁ := eq397551
       have r₂ := eq382418
       grind)
    | exact resolve eq397551 eq382418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382418 eq397551
  have eq400024 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x X1
       have i₂ := eq397586
       grind)
    | exact superpose eq397586 eq8
    | exact resolve eq8 eq397586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400025 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq397586
       grind)
    | exact superpose eq397586 eq8
    | exact resolve eq8 eq397586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400030 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 x
       have i₂ := eq397586
       grind)
    | exact superpose eq397586 eq20
    | exact resolve eq20 eq397586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq400034 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1 x
       have i₂ := eq397586
       grind)
    | exact superpose eq397586 eq24
    | exact resolve eq24 eq397586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq402958 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq400024 X0 x
       have i₂ := eq397586
       grind)
    | exact superpose eq397586 eq400024
    | exact resolve eq400024 eq397586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403597 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) y) = (k (M.op (M.op X0 X0) y) (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq525 X0 X1 (M.op X1 X1)
       have i₂ := eq400024 (M.op X1 X1) X1
       grind)
    | exact superpose eq400024 eq525
    | exact resolve eq525 eq400024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq403634 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = X1 ∨ (σ (M.op (M.op X0 X0) X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2568 X1 (M.op X0 X0)
       have i₂ := eq400024 (M.op X0 X0) X0
       grind)
    | exact superpose eq400024 eq2568
    | (have j0 := eq2568 X1 (M.op X0 X0)
       grind)
    | exact resolve eq2568 eq400024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568
  have eq403807 : ∀ X0 X1 : G, (M.op y y) = X1 ∨ (σ (M.op (M.op X0 X0) X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq403634 X0 X1
       have i₂ := eq400030 X0 y
       grind)
    | exact superpose eq400030 eq403634
    | (have j0 := eq403634 X0 X1
       grind)
    | exact resolve eq403634 eq400030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403634
  have eq403839 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (k (M.op (M.op X0 X0) y) (M.op (M.op X1 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq403597 X0 X1 x
       have i₂ := eq400034 (M.op X1 X1) x
       grind)
    | exact superpose eq400034 eq403597
    | exact resolve eq403597 eq400034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403597
  have eq404119 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (σ (M.op y X1)) ∨ (M.op y y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq403807 X0 X1
       have i₂ := eq400030 X0 X1
       grind)
    | exact superpose eq400030 eq403807
    | (have j0 := eq403807 X0 X1
       grind)
    | exact resolve eq403807 eq400030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403807
  have eq404130 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (k (M.op (M.op X0 X0) y) (M.op y (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq403839 X0 X1
       have i₂ := eq402958 (M.op X1 X1)
       grind)
    | exact superpose eq402958 eq403839
    | exact resolve eq403839 eq402958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403839
  have eq404336 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (k (M.op (M.op X0 X0) y) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq404130 X0 x
       have i₂ := eq400034 y x
       grind)
    | exact superpose eq400034 eq404130
    | exact resolve eq404130 eq400034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404130
  have eq404494 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (k (M.op y (M.op X0 X0)) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq404336 X0
       have i₂ := eq402958 (M.op X0 X0)
       grind)
    | exact superpose eq402958 eq404336
    | exact resolve eq404336 eq402958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404336
  have eq404592 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq404494 x
       have i₂ := eq400034 y x
       grind)
    | exact superpose eq400034 eq404494
    | exact resolve eq404494 eq400034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404494
  have eq409667 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = (M.op y X1) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq400025 X1 (σ X0)
       have i₂ := eq1250 X0 X0
       grind)
    | exact superpose eq1250 eq400025
    | (have j1 := eq1250 X0 X0
       grind)
    | exact resolve eq400025 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq400025
  have eq439872 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) := by
    first
    | (have i₁ := eq308033 (M.op y y)
       have i₂ := eq404592
       grind)
    | exact superpose eq404592 eq308033
    | (have j0 := eq308033 (M.op y y)
       grind)
    | (have r₁ := eq308033 (M.op y y)
       have r₂ := eq404592
       grind)
    | exact resolve eq308033 eq404592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308033
  have eq439873 : (M.op y y) = (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) := by grind
  clear eq439872
  have eq468946 : (τ (M.op y y)) = (M.op (τ (M.op y y)) (τ (M.op y y))) := by
    first
    | (have i₁ := eq9 (M.op (τ (M.op y y)) (τ (M.op y y)))
       have i₂ := eq439873
       grind)
    | exact superpose eq439873 eq9
    | exact resolve eq9 eq439873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470469 : ∀ X0 : G, (M.op X0 y) = (M.op (τ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq400024 X0 (τ (M.op y y))
       have i₂ := eq468946
       grind)
    | exact superpose eq468946 eq400024
    | exact resolve eq400024 eq468946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470471 : ∀ X0 : G, (M.op y X0) = (M.op (τ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq400030 (τ (M.op y y)) X0
       have i₂ := eq468946
       grind)
    | exact superpose eq468946 eq400030
    | exact resolve eq400030 eq468946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471031 : (τ (M.op y y)) = (M.op (τ (M.op y y)) y) := by
    first
    | (have i₁ := eq468946
       have i₂ := eq470469 (τ (M.op y y))
       grind)
    | exact superpose eq470469 eq468946
    | exact resolve eq468946 eq470469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468946
  have eq471032 : (M.op y y) = (σ (M.op (τ (M.op y y)) y)) := by
    first
    | (have i₁ := eq439873
       have i₂ := eq470469 (τ (M.op y y))
       grind)
    | exact superpose eq470469 eq439873
    | exact resolve eq439873 eq470469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439873 eq470469
  have eq471456 : (M.op y y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq471032
       have i₂ := eq470471 y
       grind)
    | exact superpose eq470471 eq471032
    | exact resolve eq471032 eq470471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471032
  have eq471457 : (M.op y y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq471031
       have i₂ := eq470471 y
       grind)
    | exact superpose eq470471 eq471031
    | exact resolve eq471031 eq470471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470471 eq471031
  have eq471655 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (τ (k (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op y y) X0
       have i₂ := eq471456
       grind)
    | exact superpose eq471456 eq51
    | exact resolve eq51 eq471456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq482736 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq4136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq482737 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq482736 X0 X1
       have j1 := eq1151 X1 X0
       grind)
    | (have r₁ := eq482736 (k X1 X1) X0
       have r₂ := eq1151 X0 X1
       grind)
    | (have r₁ := eq482736 X0 (σ (k X1 X1))
       have r₂ := eq1151 (σ X0) X1
       grind)
    | (have r₁ := eq482736 X1 X0
       have r₂ := eq1151 X0 X1
       grind)
    | exact resolve eq482736 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq482736
  have eq482770 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq482737 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq482737 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq482737 eq16
    | (have j1 := eq482737 (τ X1) X0
       grind)
    | exact resolve eq16 eq482737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq482771 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq482737 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq482737 X0 (σ X0)
       grind)
    | exact superpose eq482737 eq9
    | (have j1 := eq482737 X1 X0
       grind)
    | exact resolve eq9 eq482737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482737
  have eq482792 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq482770 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq482770
    | (have j0 := eq482770 X0 X1
       grind)
    | exact resolve eq482770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482770
  have eq482803 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq482792 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq482792
    | (have j0 := eq482792 X0 X1
       grind)
    | exact resolve eq482792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482792
  have eq483003 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq4130
       have i₂ := eq482803 y x
       grind)
    | exact superpose eq482803 eq4130
    | (have j1 := eq482803 y x
       grind)
    | exact resolve eq4130 eq482803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4130 eq482803
  have eq483143 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq483003
  have eq483229 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4674 x y
       grind)
    | exact superpose eq4674 eq14
    | (have j1 := eq4674 x y
       grind)
    | exact resolve eq14 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4674
  have eq483230 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq483229
       have i₂ := eq6530
       grind)
    | exact superpose eq6530 eq483229
    | exact resolve eq483229 eq6530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6530 eq483229
  have eq483232 : (σ x) = (σ (k x x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq483230
       have r₂ := eq483143
       grind)
    | exact resolve eq483230 eq483143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483230
  have eq483456 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1246 x
       have i₂ := eq483232
       grind)
    | exact superpose eq483232 eq1246
    | (have j0 := eq1246 x
       grind)
    | (have r₁ := eq1246 x
       have r₂ := eq483232
       grind)
    | exact resolve eq1246 eq483232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483232
  have eq483471 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by grind
  clear eq483456
  have eq483715 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq51044 X0 X1
       have i₂ := eq483143
       grind)
    | exact superpose eq483143 eq51044
    | (have j0 := eq51044 X0 X1
       grind)
    | (have r₁ := eq51044 X0 X1
       have r₂ := eq483143
       grind)
    | exact resolve eq51044 eq483143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51044
  have eq483727 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) ∨ y = (k x x) := by
    intro X0 X1
    first
    | (have j0 := eq483715 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483715
  have eq483737 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq483727 X0 x
       have i₂ := eq400034 X0 x
       grind)
    | exact superpose eq400034 eq483727
    | exact resolve eq483727 eq400034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400034 eq483727
  have eq483898 : ∀ X0 : G, (M.op X0 y) = (M.op (σ x) X0) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq400024 X0 (σ x)
       have i₂ := eq483471
       grind)
    | exact superpose eq483471 eq400024
    | exact resolve eq400024 eq483471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400024
  have eq484843 : (σ (M.op x y)) ≠ (M.op (σ x) y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq483737 (σ x)
       grind)
    | exact superpose eq483737 eq14
    | exact resolve eq14 eq483737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483737
  have eq484867 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq484843
       have i₂ := eq402958 (σ x)
       grind)
    | exact superpose eq402958 eq484843
    | exact resolve eq484843 eq402958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484843
  have eq486343 : (σ x) = (M.op (σ x) y) ∨ y = (k x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq483471
       have i₂ := eq483898 (σ x)
       grind)
    | exact superpose eq483898 eq483471
    | exact resolve eq483471 eq483898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483471 eq483898
  have eq486540 : (σ x) = (M.op (σ x) y) ∨ y = (k x x) := by grind
  clear eq486343
  have eq486664 : (σ x) = (M.op y (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq486540
       have i₂ := eq402958 (σ x)
       grind)
    | exact superpose eq402958 eq486540
    | exact resolve eq486540 eq402958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486540
  have eq490787 : (σ x) ≠ (M.op y (σ x)) ∨ y = (k x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq484867
       have i₂ := eq483143
       grind)
    | exact superpose eq483143 eq484867
    | exact resolve eq484867 eq483143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483143 eq484867
  have eq490789 : (σ x) ≠ (M.op y (σ x)) ∨ y = (k x x) := by grind
  clear eq490787
  have eq490791 : y = (k x x) := by
    first
    | (have r₁ := eq490789
       have r₂ := eq486664
       grind)
    | exact resolve eq490789 eq486664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486664 eq490789
  have eq498913 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq482771 (σ X1) X0
       grind)
    | exact superpose eq482771 eq13
    | (have j1 := eq482771 (σ X1) X0
       grind)
    | exact resolve eq13 eq482771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482771
  have eq498922 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq498913 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq498913
    | (have j0 := eq498913 X0 X1
       grind)
    | exact resolve eq498913 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498913
  have eq504930 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq404592
       have i₂ := eq498922 (M.op y y) X0
       grind)
    | (have i₁ := eq404592
       have i₂ := eq498922 X0 (k (M.op y y) (M.op y y))
       grind)
    | exact superpose eq498922 eq404592
    | (have j1 := eq498922 (M.op y y) X0
       grind)
    | exact resolve eq404592 eq498922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404592 eq498922
  have eq505154 : ∀ X0 : G, (M.op (M.op y y) (σ X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq504930 X0
       have i₂ := eq471456
       grind)
    | exact superpose eq471456 eq504930
    | (have j0 := eq504930 X0
       grind)
    | exact resolve eq504930 eq471456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504930
  have eq505184 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq505154 X0
       have i₂ := eq400030 y (σ X0)
       grind)
    | exact superpose eq400030 eq505154
    | (have j0 := eq505154 X0
       grind)
    | exact resolve eq505154 eq400030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400030 eq505154
  have eq522927 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq409667 x x
       have i₂ := eq490791
       grind)
    | exact superpose eq490791 eq409667
    | exact resolve eq409667 eq490791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409667
  have eq523364 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq522927 (σ x)
       grind)
    | exact superpose eq522927 eq14
    | exact resolve eq14 eq522927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522927
  have eq596092 : ∀ X0 : G, (τ (M.op y y)) = (k (M.op y y) (τ (M.op X0 X0))) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq471655 (M.op X0 X0)
       have i₂ := eq157845 X0
       grind)
    | exact superpose eq157845 eq471655
    | exact resolve eq471655 eq157845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157845 eq471655
  have eq596094 : ∀ X0 : G, (M.op y y) = (k (M.op y y) (τ (M.op X0 X0))) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq596092 X0
       have i₂ := eq471457
       grind)
    | exact superpose eq471457 eq596092
    | exact resolve eq596092 eq471457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471457 eq596092
  have eq596107 : ∀ X0 : G, (M.op y y) = (k (M.op y y) (τ (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq596094 X0
       have i₂ := eq490791
       grind)
    | exact superpose eq490791 eq596094
    | (have j0 := eq596094 X0
       grind)
    | exact resolve eq596094 eq490791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596094
  have eq596256 : ∀ X0 : G, (σ (M.op y y)) = (k (σ (M.op y y)) (M.op X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17 (M.op X0 X0) (M.op y y)
       have i₂ := eq596107 X0
       grind)
    | exact superpose eq596107 eq17
    | exact resolve eq17 eq596107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq596107
  have eq596272 : ∀ X0 : G, (M.op y y) = (k (M.op y y) (M.op X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq596256 X0
       have i₂ := eq471456
       grind)
    | exact superpose eq471456 eq596256
    | exact resolve eq596256 eq471456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471456 eq596256
  have eq653701 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq404119 y X0
       have i₂ := eq505184 X0
       grind)
    | exact superpose eq505184 eq404119
    | (have j0 := eq404119 X0 X0
       have j1 := eq505184 X0
       grind)
    | exact resolve eq404119 eq505184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404119 eq505184
  have eq653706 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq653701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653701
  have eq654431 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq653706 X0
       have i₂ := eq402958 X0
       grind)
    | (have i₁ := eq653706 y
       have i₂ := eq402958 y
       grind)
    | exact superpose eq402958 eq653706
    | (have j0 := eq653706 X0
       grind)
    | exact resolve eq653706 eq402958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402958 eq653706
  have eq659467 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq523364
       have i₂ := eq654431 x
       grind)
    | exact superpose eq654431 eq523364
    | (have j1 := eq654431 x
       grind)
    | (have r₁ := eq523364
       have r₂ := eq654431 x
       grind)
    | exact resolve eq523364 eq654431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523364 eq654431
  have eq659485 : x = (M.op y y) ∨ x = y := by grind
  clear eq659467
  have eq660783 : x = (k x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq596272 y
       have i₂ := eq659485
       grind)
    | exact superpose eq659485 eq596272
    | exact resolve eq596272 eq659485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596272 eq659485
  have eq660789 : x = (k x x) ∨ x = y := by grind
  clear eq660783
  have eq660908 : x = (k x x) := by
    first
    | (have r₁ := eq660789
       have r₂ := eq126754
       grind)
    | exact resolve eq660789 eq126754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126754 eq660789
  have eq661415 : x = y := by
    first
    | (have i₁ := eq490791
       have i₂ := eq660908
       grind)
    | exact superpose eq660908 eq490791
    | exact resolve eq490791 eq660908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490791
  have eq661463 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1246 x
       have i₂ := eq660908
       grind)
    | exact superpose eq660908 eq1246
    | (have j0 := eq1246 x
       grind)
    | exact resolve eq1246 eq660908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246 eq660908
  have eq661668 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq661463
  have eq661870 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq661415
       grind)
    | exact superpose eq661415 eq14
    | exact resolve eq14 eq661415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662618 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq661870
       have i₂ := eq397586
       grind)
    | exact superpose eq397586 eq661870
    | exact resolve eq661870 eq397586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397586 eq661870
  have eq662752 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq662618
       have i₂ := eq661668
       grind)
    | exact superpose eq661668 eq662618
    | exact resolve eq662618 eq661668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661668 eq662618
  have eq662805 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq662752
       have i₂ := eq661415
       grind)
    | exact superpose eq661415 eq662752
    | exact resolve eq662752 eq661415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661415 eq662752
  have eq662806 : False := by grind
  exact eq662806

/-- `Equation4497`: `x ◇ (y ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4497 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4497 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4497.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) X3
       have i₂ := eq8 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X0 X0) X3
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | (have i₁ := eq8 (M.op x x) X1 x
       have i₂ := eq8 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | (have i₁ := eq8 (M.op X1 X1) X1 X2
       have i₂ := eq8 (M.op X2 X2) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X2 X2) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X0) X1 X3
       have i₂ := eq8 (M.op X3 X3) X0 X2
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) = (M.op X1 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq36 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq83 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq159 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq41 X1 (σ X0) X2
       grind)
    | exact superpose eq41 eq48
    | (have j1 := eq41 X1 X1 X2
       grind)
    | exact resolve eq48 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq41 X1 (τ X0) X2
       grind)
    | exact superpose eq41 eq15
    | (have j1 := eq41 X1 X1 X2
       grind)
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq164 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq41 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq41 eq13
    | (have j1 := eq41 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq170 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = X0 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq160
    | (have j0 := eq160 X0 X1 X2
       grind)
    | exact resolve eq160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq171 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq159 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq159
    | (have j0 := eq159 X0 X1 X2
       grind)
    | exact resolve eq159 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq174 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ X1 ∨ (k X1 (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169 X1 (M.op X2 X2)
       have i₂ := eq8 X1 X2 X0
       grind)
    | (have i₁ := eq169 (M.op X2 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq169
    | (have j0 := eq169 X1 (M.op X2 X2)
       grind)
    | (have r₁ := eq169 (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)
       have r₂ := eq8 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact resolve eq169 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq206 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op X3 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 (M.op X1 X1) X4 X3 X2
       have i₂ := eq8 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq18 (M.op X0 X0) X4 X3 X2
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op X3 X3)) X4 X1
       have i₂ := eq18 X2 X3 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq8 X2 X1 X3
       have i₂ := eq18 X0 X1 X2 X3
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq962 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op X2 X2) X3) = (M.op X3 (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq35 (σ X1) X3 X2 (σ X0)
       grind)
    | exact superpose eq35 eq13
    | (have j1 := eq35 (σ X1) X3 X2 X3
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1066 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 (σ X0)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171 X1 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq171
    | (have j0 := eq171 X0 (σ X0) X2
       grind)
    | exact resolve eq171 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq1257 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq39 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq11 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1328 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1257 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1257 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1349 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1328 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1328
    | (have j0 := eq1328 (τ X0) X1
       grind)
    | exact resolve eq1328 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1357 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1349 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1349
    | (have j0 := eq1349 X0 X1
       grind)
    | exact resolve eq1349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1362 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1357 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1357
    | (have j0 := eq1357 X0 X1
       grind)
    | exact resolve eq1357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1526 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1362 (τ X0) X1
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq1362
    | (have j0 := eq1362 (τ X0) X1
       grind)
    | exact resolve eq1362 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1362
  have eq1954 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40
    | (have j0 := eq40 X0 X1
       grind)
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2074 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1954 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1954
    | (have j0 := eq1954 X0 X1
       grind)
    | exact resolve eq1954 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq3526 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1324 X0
       have i₂ := eq170 X1 X0 X0
       grind)
    | exact superpose eq170 eq1324
    | (have j0 := eq1324 X0
       have j1 := eq170 X1 X0 x
       grind)
    | exact resolve eq1324 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq3547 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1324 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1324
    | (have j0 := eq1324 (τ X0)
       grind)
    | exact resolve eq1324 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq3563 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3547 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3547
    | (have j0 := eq3547 X0
       grind)
    | exact resolve eq3547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq3570 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3526 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq3526 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq3526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq3571 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3563 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3563
    | (have j0 := eq3563 X0
       grind)
    | exact resolve eq3563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563
  have eq3935 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3570 X0 X1
       have i₂ := eq2074 X2 X0
       grind)
    | exact superpose eq2074 eq3570
    | (have j0 := eq3570 X0 X1
       have j1 := eq2074 X2 X0
       grind)
    | exact resolve eq3570 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3570
  have eq3963 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3935 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3935
  have eq4882 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq164 x y X0
       grind)
    | exact superpose eq164 eq14
    | (have j1 := eq164 X0 y X0
       grind)
    | exact resolve eq14 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq4986 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq4882 X0
       have j1 := eq3963 y X0 x
       grind)
    | (have r₁ := eq4882 X0
       have r₂ := eq3963 y x x
       grind)
    | exact resolve eq4882 eq3963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963 eq4882
  have eq5022 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3571 (σ y)
       have i₂ := eq4986 (σ y)
       grind)
    | exact superpose eq4986 eq3571
    | (have j0 := eq3571 (σ y)
       grind)
    | (have r₁ := eq3571 (σ y)
       have r₂ := eq4986 (σ y)
       grind)
    | exact resolve eq3571 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5024 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1526 (σ y) X0
       have i₂ := eq4986 (σ y)
       grind)
    | exact superpose eq4986 eq1526
    | (have j0 := eq1526 (σ y) X0
       grind)
    | exact resolve eq1526 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526 eq4986
  have eq5049 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq5024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024
  have eq5051 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5022
  have eq5059 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq5049 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5049
    | exact resolve eq5049 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5049
  have eq5213 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3571 y
       have i₂ := eq5059 y
       grind)
    | exact superpose eq5059 eq3571
    | (have j0 := eq3571 y
       grind)
    | (have r₁ := eq3571 y
       have r₂ := eq5059 y
       grind)
    | exact resolve eq3571 eq5059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5059
  have eq5239 : y = (M.op y y) := by grind
  clear eq5213
  have eq5389 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 y
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq19
    | exact resolve eq19 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5393 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1 y
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq23
    | exact resolve eq23 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5396 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op y (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 y X0 X1 X2
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq24
    | exact resolve eq24 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq10348 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) ∨ (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) = (k (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) (M.op X5 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq174 X1 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) X5
       have i₂ := eq206 X2 X3 X0 (M.op X1 X1) X4
       grind)
    | (have i₁ := eq174 X2 X3 X2
       have i₂ := eq206 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq206 eq174
    | (have j0 := eq174 X0 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) X5
       grind)
    | (have r₁ := eq174 X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) X2
       have r₂ := eq206 X0 X0 (M.op X0 X0) (M.op X0 X0) X0
       grind)
    | exact resolve eq174 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq206
  have eq10358 : ∀ X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) = (k (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op X4 X4)) (M.op X5 X5)) := by
    intro X2 X3 X4 X5
    first
    | (have j0 := eq10348 x x X2 X3 X4 X5
       grind)
    | (have r₁ := eq10348 x x X2 X3 X4 X5
       have r₂ := eq263 x x X2 X3 X4
       grind)
    | (have r₁ := eq10348 (M.op X3 X3) X4 X2 X2 x X5
       have r₂ := eq263 (M.op X2 X2) x X3 X3 X4
       grind)
    | exact resolve eq10348 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq10348
  have eq10656 : ∀ X2 X3 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) y) = (k (M.op (M.op (M.op X2 X2) (M.op X3 X3)) y) (M.op X5 X5)) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq10358 X2 X3 x X5
       have i₂ := eq5393 (M.op (M.op X2 X2) (M.op X3 X3)) x
       grind)
    | exact superpose eq5393 eq10358
    | exact resolve eq10358 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10358
  have eq10954 : ∀ X2 X5 : G, (M.op (M.op (M.op X2 X2) y) y) = (k (M.op (M.op (M.op X2 X2) y) y) (M.op X5 X5)) := by
    intro X2 X5
    first
    | (have i₁ := eq10656 X2 x X5
       have i₂ := eq5393 (M.op X2 X2) x
       grind)
    | exact superpose eq5393 eq10656
    | exact resolve eq10656 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10656
  have eq11227 : ∀ X5 : G, (M.op (M.op y y) y) = (k (M.op (M.op y y) y) (M.op X5 X5)) := by
    intro X5
    first
    | (have i₁ := eq10954 x X5
       have i₂ := eq5389 x y
       grind)
    | exact superpose eq5389 eq10954
    | exact resolve eq10954 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10954
  have eq11485 : ∀ X5 : G, (M.op y y) = (k (M.op y y) (M.op X5 X5)) := by
    intro X5
    first
    | (have i₁ := eq11227 X5
       have i₂ := eq5389 y y
       grind)
    | exact superpose eq5389 eq11227
    | exact resolve eq11227 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11227
  have eq11672 : ∀ X5 : G, y = (k y (M.op X5 X5)) := by
    intro X5
    first
    | (have i₁ := eq11485 X5
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq11485
    | exact resolve eq11485 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11485
  have eq20845 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (σ y) X1
       have i₂ := eq5051
       grind)
    | exact superpose eq5051 eq8
    | exact resolve eq8 eq5051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20846 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (σ y)
       have i₂ := eq5051
       grind)
    | exact superpose eq5051 eq8
    | exact resolve eq8 eq5051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20851 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 (σ y)
       have i₂ := eq5051
       grind)
    | exact superpose eq5051 eq19
    | exact resolve eq19 eq5051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20855 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1 (σ y)
       have i₂ := eq5051
       grind)
    | exact superpose eq5051 eq23
    | exact resolve eq23 eq5051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq20966 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq20855 X0 x
       have i₂ := eq5393 X0 x
       grind)
    | exact superpose eq5393 eq20855
    | exact resolve eq20855 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20855
  have eq20970 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq20851 x X1
       have i₂ := eq5389 x X1
       grind)
    | exact superpose eq5389 eq20851
    | exact resolve eq20851 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20851
  have eq20974 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq20846 X0 x
       have i₂ := eq5393 X0 x
       grind)
    | exact superpose eq5393 eq20846
    | exact resolve eq20846 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20846
  have eq20975 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq20845 X0 x
       have i₂ := eq5389 x X0
       grind)
    | exact superpose eq5389 eq20845
    | exact resolve eq20845 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20845
  have eq33318 : (σ y) = (M.op (σ y) y) := by
    first
    | (have i₁ := eq5051
       have i₂ := eq20966 (σ y)
       grind)
    | exact superpose eq20966 eq5051
    | exact resolve eq5051 eq20966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5051
  have eq33323 : (σ y) = (M.op y y) := by
    first
    | (have i₁ := eq33318
       have i₂ := eq20970 y
       grind)
    | exact superpose eq20970 eq33318
    | exact resolve eq33318 eq20970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33318
  have eq33449 : y = (σ y) := by
    first
    | (have i₁ := eq33323
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq33323
    | exact resolve eq33323 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33323
  have eq37817 : ∀ X0 : G, (k y (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq33449
       grind)
    | exact superpose eq33449 eq13
    | exact resolve eq13 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37831 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq48 y X0
       have i₂ := eq33449
       grind)
    | exact superpose eq33449 eq48
    | exact resolve eq48 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq49366 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq20970 X0
       have i₂ := eq20974 X0
       grind)
    | exact superpose eq20974 eq20970
    | exact resolve eq20970 eq20974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20974
  have eq57136 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20975 (σ x)
       grind)
    | exact superpose eq20975 eq14
    | exact resolve eq14 eq20975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20975
  have eq136390 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (M.op X2 X2) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq962 X0 X1 X2 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq136391 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op y (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136390 X0 X1 x
       have i₂ := eq5389 x (σ X0)
       grind)
    | exact superpose eq5389 eq136390
    | (have j0 := eq136390 X0 X1 x
       grind)
    | exact resolve eq136390 eq5389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5389 eq136390
  have eq144067 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1066 X0 X1 y
       have i₂ := eq37817 X0
       grind)
    | exact superpose eq37817 eq1066
    | (have j0 := eq1066 X0 X1 x
       grind)
    | exact resolve eq1066 eq37817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq37817
  have eq147593 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37831 X0
       have i₂ := eq12 y X0
       grind)
    | exact superpose eq12 eq37831
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq37831 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37831
  have eq645644 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2074 y X0
       have i₂ := eq144067 X0 X1
       grind)
    | exact superpose eq144067 eq2074
    | (have j0 := eq2074 X0 X0
       have j1 := eq144067 X0 X1
       grind)
    | exact resolve eq2074 eq144067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074 eq144067
  have eq645733 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq645644 X0 X1
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq645644 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq645644 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645644
  have eq649516 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 y)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq147593 X0
       have i₂ := eq49366 X0
       grind)
    | (have i₁ := eq147593 y
       have i₂ := eq49366 y
       grind)
    | exact superpose eq49366 eq147593
    | (have j0 := eq147593 X0
       grind)
    | exact resolve eq147593 eq49366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147593
  have eq687104 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq645733 X0 X1
       have i₂ := eq49366 X0
       grind)
    | (have i₁ := eq645733 y X1
       have i₂ := eq49366 y
       grind)
    | exact superpose eq49366 eq645733
    | (have j0 := eq645733 X0 X1
       grind)
    | exact resolve eq645733 eq49366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49366 eq645733
  have eq689654 : ∀ X0 : G, (M.op X0 y) = (σ (k y (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 y)
       have i₂ := eq649516 X0
       grind)
    | exact superpose eq649516 eq10
    | (have j1 := eq649516 X0
       grind)
    | exact resolve eq10 eq649516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649516
  have eq689760 : ∀ X0 : G, (M.op X0 y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq689654 X0
       have i₂ := eq16 X0 y
       grind)
    | exact superpose eq16 eq689654
    | (have j0 := eq689654 X0
       grind)
    | exact resolve eq689654 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq689654
  have eq689771 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq689760 X0
       have i₂ := eq33449
       grind)
    | exact superpose eq33449 eq689760
    | (have j0 := eq689760 X0
       grind)
    | exact resolve eq689760 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689760
  have eq690946 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op y (M.op X2 X2)) ∨ (M.op X0 y) = (k y X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5396 X2 X0 X1
       have i₂ := eq689771 X0
       grind)
    | exact superpose eq689771 eq5396
    | (have j1 := eq689771 X0
       grind)
    | exact resolve eq5396 eq689771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5396 eq689771
  have eq691052 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y y) ∨ (M.op X0 y) = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq690946 X0 X1 x
       have i₂ := eq5393 y x
       grind)
    | exact superpose eq5393 eq690946
    | (have j0 := eq690946 X0 X1 x
       grind)
    | exact resolve eq690946 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690946
  have eq691126 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = y ∨ (M.op X0 y) = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq691052 X0 X1
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq691052
    | (have j0 := eq691052 X0 X1
       grind)
    | exact resolve eq691052 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691052
  have eq691171 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq691126 X0 x
       have i₂ := eq5393 X0 x
       grind)
    | exact superpose eq5393 eq691126
    | (have j0 := eq691126 X0 x
       grind)
    | exact resolve eq691126 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5393 eq691126
  have eq747433 : ∀ X0 : G, (σ y) ≠ (M.op y (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq136391 y (M.op x x)
       have i₂ := eq11672 x
       grind)
    | exact superpose eq11672 eq136391
    | exact resolve eq136391 eq11672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11672 eq136391
  have eq747442 : ∀ X0 : G, (σ y) ≠ (M.op y y) ∨ (σ y) = (M.op (σ y) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq747433 X0
       have i₂ := eq20966 y
       grind)
    | exact superpose eq20966 eq747433
    | (have j0 := eq747433 X0
       grind)
    | exact resolve eq747433 eq20966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20966 eq747433
  have eq747463 : ∀ X0 : G, y ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq747442 X0
       have i₂ := eq5239
       grind)
    | exact superpose eq5239 eq747442
    | (have j0 := eq747442 X0
       grind)
    | exact resolve eq747442 eq5239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5239 eq747442
  have eq747482 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq747463 X0
       grind)
    | (have r₁ := eq747463 X0
       have r₂ := eq33449
       grind)
    | exact resolve eq747463 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747463
  have eq747498 : ∀ X0 : G, (σ y) = (M.op y (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq747482 X0
       have i₂ := eq20970 (σ (M.op X0 X0))
       grind)
    | exact superpose eq20970 eq747482
    | exact resolve eq747482 eq20970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20970 eq747482
  have eq747507 : ∀ X0 : G, y = (M.op y (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq747498 X0
       have i₂ := eq33449
       grind)
    | exact superpose eq33449 eq747498
    | exact resolve eq747498 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747498
  have eq748235 : ∀ X0 : G, (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq57136
       have i₂ := eq687104 x X0
       grind)
    | exact superpose eq687104 eq57136
    | (have j1 := eq687104 x X0
       grind)
    | (have r₁ := eq57136
       have r₂ := eq687104 x x
       grind)
    | exact resolve eq57136 eq687104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687104
  have eq748260 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq748235 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748235
  have eq748418 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3571 x
       have i₂ := eq748260 x
       grind)
    | exact superpose eq748260 eq3571
    | (have j0 := eq3571 x
       grind)
    | (have r₁ := eq3571 x
       have r₂ := eq748260 x
       grind)
    | exact resolve eq3571 eq748260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3571
  have eq748715 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq691171 x
       have i₂ := eq748260 y
       grind)
    | exact superpose eq748260 eq691171
    | (have j0 := eq691171 x
       grind)
    | exact resolve eq691171 eq748260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691171 eq748260
  have eq748723 : y = (M.op x y) := by grind
  clear eq748715
  have eq748725 : x = (M.op x x) := by grind
  clear eq748418
  have eq749127 : (σ y) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq57136
       have i₂ := eq748723
       grind)
    | exact superpose eq748723 eq57136
    | exact resolve eq57136 eq748723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57136 eq748723
  have eq749179 : y ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq749127
       have i₂ := eq33449
       grind)
    | exact superpose eq33449 eq749127
    | exact resolve eq749127 eq33449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33449 eq749127
  have eq749418 : y = (M.op y (σ x)) := by
    first
    | (have i₁ := eq747507 x
       have i₂ := eq748725
       grind)
    | exact superpose eq748725 eq747507
    | exact resolve eq747507 eq748725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747507 eq748725
  have eq749430 : False := by grind
  exact eq749430

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation450 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law450 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq84 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq88 (σ X0) (σ X1)
       grind)
    | exact superpose eq88 eq13
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq104
    | exact resolve eq104 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq104
  have eq1046 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109 x y
       grind)
    | exact superpose eq109 eq14
    | (have r₁ := eq14
       have r₂ := eq109 x y
       grind)
    | exact resolve eq14 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1069 : False := by grind
  exact eq1069

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4502 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4502 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X2 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8 X3 (M.op X2 X2) X4 X5
       have i₂ := eq8 (M.op X2 X2) X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 x X2 X4 X5
       have i₂ := eq8 x X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq8 X2 X1 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X2 X3) ∨ (k X1 (M.op X2 X3)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X1 (M.op X2 X3)
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X1 (M.op X2 X3)
       grind)
    | (have r₁ := eq11 (M.op X1 X1) (M.op (M.op X2 X3) X1)
       have r₂ := eq8 (M.op (M.op X2 X3) X1) X1 X2 X3
       grind)
    | (have r₁ := eq11 X1 (M.op X0 (M.op X1 X1))
       have r₂ := eq8 X0 X1 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq108 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (M.op (M.op X3 X4) (M.op X1 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) X3 X4
       have i₂ := eq22 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X1 X1) X3 X4
       have i₂ := eq22 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq12 (σ X0) X1
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 X6 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X6 (M.op X3 X3)) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq22 (M.op x x) X3 X6
       have i₂ := eq17 X1 X2 X3 X0 x x
       grind)
    | (have i₁ := eq22 X3 (M.op X0 X1) X2
       have i₂ := eq17 X0 X1 (M.op X0 X1) X3 x x
       grind)
    | exact superpose eq17 eq22
    | exact resolve eq22 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq22
  have eq586 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq25 X0 X0 X1 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq602 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq586 X2 x
       have i₂ := eq8 x X2 X0 X1
       grind)
    | exact superpose eq8 eq586
    | exact resolve eq586 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq632 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | (have j0 := eq31 X1 X0
       have j1 := eq31 X1 X0
       grind)
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq31 X1 X0
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq665 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq653 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq666 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq665
    | (have j0 := eq665 X0 X1
       grind)
    | exact resolve eq665 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq667 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq634
    | (have j0 := eq634 X0 X1
       grind)
    | exact resolve eq634 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq4170 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq4223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4170 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq4170
    | (have j0 := eq4170 X0 X1
       grind)
    | exact resolve eq4170 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4170
  have eq6421 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq666
    | exact resolve eq666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq6503 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6421 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6421
    | (have j0 := eq6421 X0 X1
       grind)
    | exact resolve eq6421 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6421
  have eq6505 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6503 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6503
    | (have j0 := eq6503 X0 X1
       grind)
    | exact resolve eq6503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6503
  have eq17841 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6505 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6505
    | exact resolve eq6505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6505
  have eq19062 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17841 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17841
  have eq24857 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq667 (τ X0) (τ X1)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq667
    | (have j0 := eq667 (τ X0) (τ X1)
       grind)
    | exact resolve eq667 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq667
  have eq24894 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24857 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq24857
    | (have j0 := eq24857 X0 X1
       grind)
    | exact resolve eq24857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24857
  have eq24906 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24894 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24894
    | (have j0 := eq24894 X0 X1
       grind)
    | exact resolve eq24894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24894
  have eq24915 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24906 X0 X1
       have i₂ := eq16 X0 (τ X1)
       grind)
    | exact superpose eq16 eq24906
    | (have j0 := eq24906 X0 X1
       grind)
    | exact resolve eq24906 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24906
  have eq24924 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24915 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24915
    | (have j0 := eq24915 X0 X1
       grind)
    | exact resolve eq24915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24915
  have eq24927 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24924 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24924
    | (have j0 := eq24924 X0 X1
       grind)
    | exact resolve eq24924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24924
  have eq24928 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24927 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24927
    | (have j0 := eq24927 X0 X1
       grind)
    | exact resolve eq24927 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24927
  have eq24929 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24928 X0 X1
       have j1 := eq19062 X1 X0
       grind)
    | (have r₁ := eq24928 X1 X0
       have r₂ := eq19062 X0 X1
       grind)
    | (have r₁ := eq24928 X0 X1
       have r₂ := eq19062 X0 X1
       grind)
    | exact resolve eq24928 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24928
  have eq24941 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24929 X0 (M.op (M.op X1 X2) X0)
       have i₂ := eq602 X1 X2 X0
       grind)
    | exact superpose eq602 eq24929
    | (have j0 := eq24929 X0 (M.op (M.op X1 X2) X0)
       grind)
    | (have r₁ := eq24929 X2 (M.op (M.op X0 X1) X2)
       have r₂ := eq602 X0 X1 X2
       grind)
    | exact resolve eq24929 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq24929
  have eq24983 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq24941 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24941
  have eq40888 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq632 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq632
    | exact resolve eq632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq41087 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40888 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq40888
    | (have j0 := eq40888 X0 X1
       grind)
    | exact resolve eq40888 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq40888
  have eq41091 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41087 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq41087
    | (have j0 := eq41087 X0 X1
       grind)
    | exact resolve eq41087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq41087
  have eq41093 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq41091 X0 X1
       have j1 := eq11 X0 (σ X1)
       grind)
    | (have r₁ := eq41091 X0 X1
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq41091 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41091
  have eq41140 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X1)
       have i₂ := eq41093 (σ X0) X1
       grind)
    | exact superpose eq41093 eq39
    | (have j1 := eq41093 (σ X0) X1
       grind)
    | exact resolve eq39 eq41093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq41093
  have eq41214 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41140 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq41140
    | (have j0 := eq41140 X0 X1
       grind)
    | exact resolve eq41140 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41140
  have eq41237 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41214 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq41214
    | (have j0 := eq41214 X0 X1
       grind)
    | exact resolve eq41214 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41214
  have eq41245 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41237 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq41237
    | (have j0 := eq41237 X0 X1
       grind)
    | exact resolve eq41237 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41237
  have eq46163 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq41245 y x
       grind)
    | exact superpose eq41245 eq14
    | (have j1 := eq41245 y x
       grind)
    | exact resolve eq14 eq41245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41245
  have eq46645 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq46163
       have i₂ := eq4223 x y
       grind)
    | exact superpose eq4223 eq46163
    | (have j1 := eq4223 x y
       grind)
    | (have r₁ := eq46163
       have r₂ := eq4223 x y
       grind)
    | exact resolve eq46163 eq4223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4223 eq46163
  have eq46646 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq46645
  have eq46649 : y = (k y x) := by
    first
    | (have j1 := eq19062 y x
       grind)
    | (have r₁ := eq46646
       have r₂ := eq19062 y x
       grind)
    | exact resolve eq46646 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19062 eq46646
  have eq46819 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq46649
       grind)
    | exact superpose eq46649 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq46649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49714 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 y x
       have i₂ := eq46819
       grind)
    | exact superpose eq46819 eq8
    | exact resolve eq8 eq46819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49719 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 y x
       have i₂ := eq46819
       grind)
    | exact superpose eq46819 eq18
    | exact resolve eq18 eq46819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49746 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op X0 (M.op y X1)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 y x X1 X2
       have i₂ := eq46819
       grind)
    | exact superpose eq46819 eq176
    | exact resolve eq176 eq46819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq49803 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24983 X0 y x
       have i₂ := eq46819
       grind)
    | exact superpose eq46819 eq24983
    | exact resolve eq24983 eq46819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122884 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op y X1)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq49714 x X1
       have i₂ := eq49746 X0 X1 x
       grind)
    | (have i₁ := eq49714 X0 y
       have i₂ := eq49746 X0 y x
       grind)
    | exact superpose eq49746 eq49714
    | exact resolve eq49714 eq49746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49714 eq49746
  have eq123177 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op y X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq122884 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122884
  have eq123202 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq123177 X0 x
       have i₂ := eq46819
       grind)
    | exact superpose eq46819 eq123177
    | exact resolve eq123177 eq46819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46819
  have eq123645 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq123202 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123202
  have eq124117 : y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49803 y
       have i₂ := eq123645 y
       grind)
    | exact superpose eq123645 eq49803
    | exact resolve eq49803 eq123645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49803
  have eq124230 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq124238 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq124117
  have eq124302 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq664 y
       have i₂ := eq124238
       grind)
    | exact superpose eq124238 eq664
    | (have j0 := eq664 y
       grind)
    | exact resolve eq664 eq124238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124238
  have eq124326 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq124302
  have eq126098 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq49719 (σ y) (σ y) X0
       have i₂ := eq124326
       grind)
    | exact superpose eq124326 eq49719
    | exact resolve eq49719 eq124326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49719
  have eq126103 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq126098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126098
  have eq127135 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124326
       have i₂ := eq126103 (σ y)
       grind)
    | exact superpose eq126103 eq124326
    | exact resolve eq124326 eq126103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124326 eq126103
  have eq127379 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x y) := by grind
  clear eq127135
  have eq127403 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq123177 X0 (σ y)
       have i₂ := eq127379
       grind)
    | exact superpose eq127379 eq123177
    | exact resolve eq123177 eq127379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123177 eq127379
  have eq127473 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq127403 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127403
  have eq127695 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq127473 (σ x)
       grind)
    | exact superpose eq127473 eq14
    | exact resolve eq14 eq127473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127473
  have eq127813 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127695
       have i₂ := eq123645 x
       grind)
    | exact superpose eq123645 eq127695
    | exact resolve eq127695 eq123645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123645 eq127695
  have eq127815 : x = y ∨ x = (M.op x y) := by grind
  clear eq127813
  have eq127816 : x = (M.op x y) := by
    first
    | (have r₁ := eq127815
       have r₂ := eq124230
       grind)
    | exact resolve eq127815 eq124230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124230 eq127815
  have eq127841 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x y
       have i₂ := eq127816
       grind)
    | exact superpose eq127816 eq8
    | exact resolve eq8 eq127816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127846 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 x y
       have i₂ := eq127816
       grind)
    | exact superpose eq127816 eq18
    | exact resolve eq18 eq127816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq128054 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24983 X0 x y
       have i₂ := eq127816
       grind)
    | exact superpose eq127816 eq24983
    | exact resolve eq24983 eq127816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24983
  have eq129209 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq108 X2 X0 X1 x x
       have i₂ := eq127841 (M.op x x) X0
       grind)
    | exact superpose eq127841 eq108
    | exact resolve eq108 eq127841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq129516 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq129209 X0 X1 x
       have i₂ := eq127841 x X0
       grind)
    | exact superpose eq127841 eq129209
    | exact resolve eq129209 eq127841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127841 eq129209
  have eq131964 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq129516 y x
       have i₂ := eq127816
       grind)
    | exact superpose eq127816 eq129516
    | exact resolve eq129516 eq127816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133912 : x = (k x x) := by
    first
    | (have i₁ := eq128054 x
       have i₂ := eq131964 x
       grind)
    | exact superpose eq131964 eq128054
    | exact resolve eq128054 eq131964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128054 eq131964
  have eq134758 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq664 x
       have i₂ := eq133912
       grind)
    | exact superpose eq133912 eq664
    | (have j0 := eq664 x
       grind)
    | exact resolve eq664 eq133912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq133912
  have eq134798 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq134758
  have eq136593 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq127846 (σ x) (σ x) X0
       have i₂ := eq134798
       grind)
    | exact superpose eq134798 eq127846
    | exact resolve eq127846 eq134798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127846
  have eq139637 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq136593 (σ y)
       grind)
    | exact superpose eq136593 eq14
    | exact resolve eq14 eq136593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139638 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq134798
       have i₂ := eq136593 (σ x)
       grind)
    | exact superpose eq136593 eq134798
    | exact resolve eq134798 eq136593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134798
  have eq140222 : (σ x) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq139637
       have i₂ := eq127816
       grind)
    | exact superpose eq127816 eq139637
    | exact resolve eq139637 eq127816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127816 eq139637
  have eq140346 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq129516 (σ x) x
       have i₂ := eq139638
       grind)
    | exact superpose eq139638 eq129516
    | exact resolve eq129516 eq139638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129516
  have eq141515 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq116 X0 (σ x)
       have i₂ := eq140346 (σ X0)
       grind)
    | exact superpose eq140346 eq116
    | (have j0 := eq116 X0 (σ x)
       grind)
    | exact resolve eq116 eq140346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq140346
  have eq141635 : ∀ X0 : G, x = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq141515 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq141515
    | (have j0 := eq141515 X0
       grind)
    | exact resolve eq141515 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141515
  have eq141916 : ∀ X0 : G, (σ x) = (M.op x (σ X0)) ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq141635 X0
       have i₂ := eq136593 (σ X0)
       grind)
    | exact superpose eq136593 eq141635
    | (have j0 := eq141635 X0
       grind)
    | exact resolve eq141635 eq136593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136593 eq141635
  have eq171913 : (σ x) ≠ (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq140222
       have i₂ := eq141916 y
       grind)
    | exact superpose eq141916 eq140222
    | (have j1 := eq141916 y
       grind)
    | (have r₁ := eq140222
       have r₂ := eq141916 y
       grind)
    | exact resolve eq140222 eq141916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141916
  have eq172013 : x = (k y x) := by grind
  clear eq171913
  have eq172105 : x = y := by
    first
    | (have i₁ := eq46649
       have i₂ := eq172013
       grind)
    | exact superpose eq172013 eq46649
    | exact resolve eq46649 eq172013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46649 eq172013
  have eq172330 : (σ x) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq140222
       have i₂ := eq172105
       grind)
    | exact superpose eq172105 eq140222
    | exact resolve eq140222 eq172105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140222 eq172105
  have eq172338 : False := by grind
  exact eq172338

/-- `Equation4513`: `x ◇ (y ◇ z) = (x ◇ y) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4513 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4513 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4513.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X0) X5) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 X3 X0 (M.op X1 x) X5
       have i₂ := eq8 X0 X1 x X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8 X0 X1 x X4
       have i₂ := eq8 X0 X1 x X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X2 x
       have i₂ := eq8 X0 X1 X3 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X1 X4 (M.op X2 x)
       have i₂ := eq8 (M.op X0 X1) X2 x X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq33 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq16
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (k X0 (M.op X1 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 (M.op X1 X3)
       have i₂ := eq23 X0 X1 X3 X2
       grind)
    | (have i₁ := eq11 X0 (M.op X1 X3)
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 X0 (M.op X1 X3)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X3))
       have r₂ := eq23 X0 X0 (M.op X0 X3) X3
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq23 X0 X0 X2 (M.op X0 X2)
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq286 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op X0 X1) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq17 X4 x x (M.op (M.op X0 X1) X3) X5
       have i₂ := eq24 X0 X1 X3 (M.op (M.op X4 x) x) X2
       grind)
    | exact superpose eq24 eq17
    | exact resolve eq17 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq24
  have eq1738 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq32 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq32 X0 X1
       grind)
    | exact resolve eq11 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1765 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1766 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1738 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq1767 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1766 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1766
    | (have j0 := eq1766 X0 X1
       grind)
    | exact resolve eq1766 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq5874 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq5924 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5874 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5874
    | (have j0 := eq5874 X0 X1
       grind)
    | exact resolve eq5874 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5874
  have eq6200 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X0 x (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq6209 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (M.op X0 (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6200 X0 (M.op X1 x)
       have i₂ := eq286 X0 X1 x X2 X3 X4
       grind)
    | exact superpose eq286 eq6200
    | exact resolve eq6200 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq6200
  have eq18891 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1767 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1767
    | exact resolve eq1767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18898 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1767 x y
       grind)
    | exact superpose eq1767 eq14
    | (have j1 := eq1767 x y
       grind)
    | exact resolve eq14 eq1767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq18993 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18891 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18891
    | (have j0 := eq18891 X0 X1
       grind)
    | exact resolve eq18891 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18891
  have eq18995 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18993 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18993
    | (have j0 := eq18993 X0 X1
       grind)
    | exact resolve eq18993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq18993
  have eq44134 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18995 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18995
    | exact resolve eq18995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18995
  have eq44993 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq44134 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44134
  have eq79675 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18898
       have i₂ := eq5924 y x
       grind)
    | exact superpose eq5924 eq18898
    | (have j1 := eq5924 y x
       grind)
    | (have r₁ := eq18898
       have r₂ := eq5924 y x
       grind)
    | exact resolve eq18898 eq5924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18898
  have eq79676 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq79675
  have eq81158 : (M.op x y) = (τ (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq79676
       grind)
    | exact superpose eq79676 eq9
    | exact resolve eq9 eq79676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79676
  have eq81215 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq81158
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq81158
    | exact resolve eq81158 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81158
  have eq82711 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 y x X0 X1
       have i₂ := eq81215
       grind)
    | exact superpose eq81215 eq8
    | exact resolve eq8 eq81215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82722 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 y X1 x
       have i₂ := eq81215
       grind)
    | exact superpose eq81215 eq23
    | exact resolve eq23 eq81215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82855 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44993 x y
       have i₂ := eq81215
       grind)
    | exact superpose eq81215 eq44993
    | (have j0 := eq44993 x y
       grind)
    | (have r₁ := eq44993 x y
       have r₂ := eq81215
       grind)
    | (have r₁ := eq44993 y x
       have r₂ := eq81215
       grind)
    | exact resolve eq44993 eq81215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44993
  have eq82861 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq82855
  have eq82863 : x = (k x y) := by
    first
    | (have j1 := eq11 x y
       grind)
    | (have r₁ := eq82861
       have r₂ := eq11 x y
       grind)
    | exact resolve eq82861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82861
  have eq83290 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5924 x y
       have i₂ := eq82863
       grind)
    | exact superpose eq82863 eq5924
    | (have j0 := eq5924 x y
       grind)
    | exact resolve eq5924 eq82863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5924
  have eq111168 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op x X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq82722 X1 (M.op x x)
       have i₂ := eq82711 x X0
       grind)
    | exact superpose eq82711 eq82722
    | exact resolve eq82722 eq82711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82722
  have eq111998 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq111168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111168
  have eq132535 : ∀ X1 : G, (M.op y x) = (M.op x X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq82711 x X1
       have i₂ := eq111998 x y
       grind)
    | exact superpose eq111998 eq82711
    | exact resolve eq82711 eq111998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82711 eq111998
  have eq132541 : ∀ X1 : G, (M.op y x) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq132535 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132535
  have eq135804 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq81215
       have i₂ := eq132541 X0
       grind)
    | exact superpose eq132541 eq81215
    | exact resolve eq81215 eq132541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81215
  have eq135807 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq83290
       have i₂ := eq132541 X0
       grind)
    | exact superpose eq132541 eq83290
    | exact resolve eq83290 eq132541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83290 eq132541
  have eq136390 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq135807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135807
  have eq136393 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq135804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135804
  have eq136948 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6209 x x x x x
       have i₂ := eq136393 (M.op (M.op (M.op (M.op x x) x) x) x)
       grind)
    | exact superpose eq136393 eq6209
    | exact resolve eq6209 eq136393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136393
  have eq137559 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1765 x
       have i₂ := eq136948
       grind)
    | exact superpose eq136948 eq1765
    | (have j0 := eq1765 x
       grind)
    | exact resolve eq1765 eq136948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136948
  have eq137568 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq137559
  have eq163648 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ x) (σ x) x x
       have i₂ := eq137568
       grind)
    | exact superpose eq137568 eq19
    | exact resolve eq19 eq137568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235785 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq137568
       have i₂ := eq163648 (σ x) X0
       grind)
    | (have i₁ := eq137568
       have i₂ := eq163648 X0 (σ x)
       grind)
    | exact superpose eq163648 eq137568
    | exact resolve eq137568 eq163648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137568 eq163648
  have eq235917 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq235785 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235785
  have eq236031 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq235917 (σ y)
       grind)
    | exact superpose eq235917 eq14
    | exact resolve eq14 eq235917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235917
  have eq236315 : y = (M.op x y) := by
    first
    | (have r₁ := eq236031
       have r₂ := eq136390 y
       grind)
    | exact resolve eq236031 eq136390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136390 eq236031
  have eq236361 : ∀ X0 X1 : G, (M.op y X1) = (M.op x (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 x y X0 X1
       have i₂ := eq236315
       grind)
    | exact superpose eq236315 eq8
    | exact resolve eq8 eq236315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236372 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 x X1 y
       have i₂ := eq236315
       grind)
    | exact superpose eq236315 eq23
    | exact resolve eq23 eq236315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq238877 : ∀ X0 X1 : G, (M.op y X1) = (M.op x (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq236361 x X1
       have i₂ := eq236361 X0 x
       grind)
    | exact superpose eq236361 eq236361
    | exact resolve eq236361 eq236361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236361
  have eq240098 : ∀ X1 : G, (M.op x y) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq238877 x X1
       have i₂ := eq236372 x (M.op y x)
       grind)
    | exact superpose eq236372 eq238877
    | exact resolve eq238877 eq236372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236372 eq238877
  have eq240106 : ∀ X1 : G, y = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq240098 X1
       have i₂ := eq236315
       grind)
    | exact superpose eq236315 eq240098
    | exact resolve eq240098 eq236315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240098
  have eq241007 : y = (k y y) := by
    first
    | (have i₁ := eq6209 y x x x x
       have i₂ := eq240106 (M.op (M.op (M.op (M.op y x) x) x) x)
       grind)
    | exact superpose eq240106 eq6209
    | exact resolve eq6209 eq240106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6209
  have eq241423 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1765 y
       have i₂ := eq241007
       grind)
    | exact superpose eq241007 eq1765
    | (have j0 := eq1765 y
       grind)
    | exact resolve eq1765 eq241007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765 eq241007
  have eq241433 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq241423
  have eq241543 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ y) (σ y) x x
       have i₂ := eq241433
       grind)
    | exact superpose eq241433 eq19
    | exact resolve eq19 eq241433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq250096 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq241433
       have i₂ := eq241543 (σ y) X0
       grind)
    | (have i₁ := eq241433
       have i₂ := eq241543 X0 (σ y)
       grind)
    | exact superpose eq241543 eq241433
    | exact resolve eq241433 eq241543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241433 eq241543
  have eq251054 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq118 (σ y) X0
       have i₂ := eq250096 (σ X0)
       grind)
    | exact superpose eq250096 eq118
    | (have j0 := eq118 (σ y) X0
       grind)
    | exact resolve eq118 eq250096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq251079 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ y)) ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq251054 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq251054
    | (have j0 := eq251054 X0
       grind)
    | exact resolve eq251054 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251054
  have eq354203 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq251079 x
       grind)
    | exact superpose eq251079 eq14
    | (have j1 := eq251079 x
       grind)
    | exact resolve eq14 eq251079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251079
  have eq354287 : (σ y) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq354203
       have i₂ := eq236315
       grind)
    | exact superpose eq236315 eq354203
    | exact resolve eq354203 eq236315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236315 eq354203
  have eq354288 : y = (k x y) := by grind
  clear eq354287
  have eq354294 : x = y := by
    first
    | (have i₁ := eq354288
       have i₂ := eq82863
       grind)
    | exact superpose eq82863 eq354288
    | exact resolve eq354288 eq82863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82863 eq354288
  have eq354313 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq354294
       grind)
    | exact superpose eq354294 eq14
    | exact resolve eq14 eq354294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354534 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq240106 x
       have i₂ := eq354294
       grind)
    | exact superpose eq354294 eq240106
    | exact resolve eq240106 eq354294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240106
  have eq354580 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq250096 X0
       have i₂ := eq354294
       grind)
    | exact superpose eq354294 eq250096
    | exact resolve eq250096 eq354294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250096 eq354294
  have eq354695 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq354313
       have i₂ := eq354534 x
       grind)
    | exact superpose eq354534 eq354313
    | exact resolve eq354313 eq354534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354313 eq354534
  have eq354750 : False := by grind
  exact eq354750
