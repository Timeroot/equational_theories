import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_pyy_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X2 (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op x X0) X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X2
       have i₂ := eq71 X0 X1
       grind)
    | (have i₁ := eq71 X1 X1
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq71
    | exact resolve eq71 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op (M.op X0 X0) X1) (M.op x X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq71 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq9
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X0 (M.op X0 X1)
       have i₂ := eq71 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq53 X0 X1 (M.op X1 X0)
       have i₂ := eq71 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq71 eq53
    | exact resolve eq53 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq181 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq180 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq180
    | (have j0 := eq180 (σ X0) (σ X1)
       grind)
    | exact resolve eq180 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq180 (τ X0) X1
       grind)
    | exact superpose eq180 eq17
    | (have j1 := eq180 (τ X0) X1
       grind)
    | exact resolve eq17 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq180 X0 (τ X1)
       grind)
    | exact superpose eq180 eq18
    | (have j1 := eq180 X0 (τ X1)
       grind)
    | exact resolve eq18 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq188 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq180 X0 (σ X1)
       grind)
    | exact superpose eq180 eq22
    | (have j1 := eq180 X0 (σ X1)
       grind)
    | exact resolve eq22 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq313 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op X3 (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) X1) (M.op x X0) X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) X0) X0 X1
       have i₂ := eq51 X0 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181 x y
       grind)
    | exact superpose eq181 eq16
    | (have j1 := eq181 x y
       grind)
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) X1) (M.op X2 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq181 X0 X0
       grind)
    | exact superpose eq181 eq9
    | (have j1 := eq181 X0 X0
       grind)
    | exact resolve eq9 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (M.op (σ X1) (σ X1)) X2) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) X2 (σ X0)
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq9
    | (have j1 := eq181 X0 X1
       grind)
    | exact resolve eq9 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X0)) = (M.op (M.op (σ X0) X2) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 (σ X0) (σ X1) X2
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq78
    | (have j1 := eq181 X0 X1
       grind)
    | exact resolve eq78 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (M.op X0 X0) X1 (M.op x X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ X0 ∨ (k X2 (M.op (M.op X0 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq71 X0 X1
       grind)
    | (have i₁ := eq67 X1 X1
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq67
    | exact resolve eq67 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq691 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq535 (M.op X0 X1) (M.op (M.op X0 X0) X0)
       have i₂ := eq51 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq51 eq535
    | exact resolve eq535 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq535
  have eq722 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq691
    | exact resolve eq691 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq735 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq722 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)
       have i₂ := eq722 X0 X1
       grind)
    | exact superpose eq722 eq722
    | exact resolve eq722 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X0 X0) X0) X2
       have i₂ := eq722 X0 X1
       grind)
    | exact superpose eq722 eq9
    | exact resolve eq9 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 X1
       have i₂ := eq9 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq735
    | exact resolve eq735 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq781 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq187
    | exact resolve eq187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq810 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq781 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq781
    | (have j0 := eq781 X0 X1
       grind)
    | exact resolve eq781 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq1046 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq772 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)
       have i₂ := eq722 X0 X1
       grind)
    | exact superpose eq722 eq772
    | exact resolve eq772 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq1055 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X0 X2
       have i₂ := eq772 X0 X1
       grind)
    | (have i₁ := eq53 X1 X1 X2
       have i₂ := eq772 X1 X1
       grind)
    | exact superpose eq772 eq53
    | exact resolve eq53 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X0) (M.op X0 X1)) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq772 X0 X1
       grind)
    | (have i₁ := eq12 X0 (M.op X1 X1)
       have i₂ := eq772 X1 X1
       grind)
    | exact superpose eq772 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X0 (M.op (M.op X0 X1) X2)
       have i₂ := eq772 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq53 X0 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq772 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq772 eq53
    | exact resolve eq53 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1125 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X0) X1)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1055 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq1055
    | exact resolve eq1055 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1055 X0 X1 (M.op (M.op X0 X0) (M.op X0 X1))
       have i₂ := eq772 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have i₁ := eq1055 X0 X0 (M.op (M.op X0 X0) X1)
       have i₂ := eq772 (M.op X0 X0) X1
       grind)
    | exact superpose eq772 eq1055
    | exact resolve eq1055 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1246 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq477
       have i₂ := eq180 x y
       grind)
    | exact superpose eq180 eq477
    | (have j1 := eq180 (σ x) (σ y)
       grind)
    | exact resolve eq477 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq1249 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1246
  have eq1250 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1249
       have i₂ := eq181 y x
       grind)
    | exact superpose eq181 eq1249
    | (have j1 := eq181 y x
       grind)
    | exact resolve eq1249 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1252 : (k (τ (σ y)) x) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq188 (σ y) x
       have i₂ := eq1249
       grind)
    | exact superpose eq1249 eq188
    | (have j0 := eq188 (σ y) x
       grind)
    | exact resolve eq188 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq1260 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq81 (σ y) (σ x) X0
       have i₂ := eq1249
       grind)
    | exact superpose eq1249 eq81
    | exact resolve eq81 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1274 : x = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1252
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1252
    | exact resolve eq1252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1275 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1274
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1274
    | exact resolve eq1274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1420 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq338 X0 X1
       have i₂ := eq71 X0 X1
       grind)
    | (have i₁ := eq338 X1 X1
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq338
    | exact resolve eq338 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq338
  have eq1923 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (k (τ X0) (τ X0))) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq482 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq482
    | exact resolve eq482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq1999 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 (σ (τ X0))) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1923 X0 X1 X2
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1923
    | (have j0 := eq1923 X0 X1 X2
       grind)
    | exact resolve eq1923 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1923
  have eq2010 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1999 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1999
    | (have j0 := eq1999 X0 X1 X2
       grind)
    | exact resolve eq1999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2067 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (M.op X0 (M.op (k X0 X0) X1)) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82 (k X0 X0) X1 (M.op x X0)
       have i₂ := eq2010 X0 X1 x
       grind)
    | exact superpose eq2010 eq82
    | (have j1 := eq2010 X0 X1 x
       grind)
    | exact resolve eq82 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq2010
  have eq2206 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (M.op (σ (τ X1)) (σ (τ X1))) X2) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq483 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq483
    | (have j0 := eq483 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq483 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq2256 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (M.op (σ (τ X1)) (σ (τ X1))) X2) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2206 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2206
    | (have j0 := eq2206 X0 X1 X2
       grind)
    | exact resolve eq2206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2263 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (k X0 X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2256 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2256
    | (have j0 := eq2256 X0 X1 X2
       grind)
    | exact resolve eq2256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq2264 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op (M.op (M.op X1 X1) X2) (k X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2263 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2263
    | (have j0 := eq2263 X0 X1 X2
       grind)
    | exact resolve eq2263 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq2265 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (k X0 X1)) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2264 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2264
    | (have j0 := eq2264 X0 X1 X2
       grind)
    | exact resolve eq2264 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq2310 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op (M.op (M.op (k X1 X0) X2) (k X1 X0)) X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 (k X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq2265 X1 X0 x
       grind)
    | exact superpose eq2265 eq81
    | (have j1 := eq2265 X1 X0 X2
       grind)
    | exact resolve eq81 eq2265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265
  have eq3889 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1260 (σ x)
       have i₂ := eq1275
       grind)
    | exact superpose eq1275 eq1260
    | exact resolve eq1260 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq1275
  have eq3919 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (k y x) := by grind
  clear eq3889
  have eq4608 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = (M.op y x) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq3919
       grind)
    | exact superpose eq3919 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq3919
       grind)
    | exact resolve eq12 eq3919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq4646 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = (M.op y x) ∨ x = (k y x) := by
    intro X0
    first
    | (have j0 := eq4608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4608
  have eq5120 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X2 (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1))))) = (σ (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1))) ∨ (τ X0) = (M.op (M.op X2 (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq185 X0 (M.op X2 (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1)))
       have i₂ := eq313 (τ X0) X1 X2
       grind)
    | exact superpose eq313 eq185
    | (have j0 := eq185 X0 (M.op X2 (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1)))
       grind)
    | exact resolve eq185 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq313
  have eq7121 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ x = (M.op y x) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq4646 (σ X0)
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq4646
    | exact resolve eq4646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646
  have eq11379 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1250
       grind)
    | exact superpose eq1250 eq16
    | exact resolve eq16 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq11471 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (M.op X0 X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2067 X0 (M.op X0 X1)
       have i₂ := eq750 X0 X1 (k X0 X0)
       grind)
    | exact superpose eq750 eq2067
    | (have j0 := eq2067 X0 X1
       grind)
    | exact resolve eq2067 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067
  have eq12990 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2))) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2)) X3) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1420 (M.op X0 X1) X0 X2
       have i₂ := eq78 X0 X1 X2
       grind)
    | (have i₁ := eq1420 (M.op X0 X2) X0 X2
       have i₂ := eq78 X0 X1 X2
       grind)
    | exact superpose eq78 eq1420
    | exact resolve eq1420 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13149 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X0 X1) X0)) (M.op (M.op (M.op X0 X1) X0) X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq78 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0) X3
       have i₂ := eq1420 X0 X1 X2
       grind)
    | exact superpose eq1420 eq78
    | exact resolve eq78 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16135 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7121 x
       grind)
    | exact superpose eq7121 eq16
    | exact resolve eq16 eq7121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7121
  have eq16249 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq810 y x
       grind)
    | (have r₁ := eq16135
       have r₂ := eq810 y x
       grind)
    | exact resolve eq16135 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq16135
  have eq16256 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq180 y x
       have i₂ := eq16249
       grind)
    | exact superpose eq16249 eq180
    | (have j0 := eq180 x y
       grind)
    | exact resolve eq180 eq16249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq16287 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq16256
  have eq16289 : (σ y) ≠ (σ y) ∨ x = (M.op y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11379
       have i₂ := eq16287
       grind)
    | exact superpose eq16287 eq11379
    | exact resolve eq11379 eq16287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11379
  have eq16292 : y ≠ y ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16287
       grind)
    | exact superpose eq16287 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16287
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16287
       grind)
    | exact resolve eq13 eq16287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16287
  have eq16333 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq16292
  have eq16336 : (σ y) ≠ (σ y) ∨ x = (M.op y x) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq16289
  have eq16337 : (σ x) = (σ (k y x)) ∨ x = (M.op y x) := by grind
  clear eq16336
  have eq21244 : x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16249
       have i₂ := eq16333
       grind)
    | exact superpose eq16333 eq16249
    | exact resolve eq16249 eq16333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16333
  have eq21303 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq21244
  have eq52462 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2310 X0 X0 (M.op X0 X1)
       have i₂ := eq11471 X0 X1
       grind)
    | exact superpose eq11471 eq2310
    | (have j0 := eq2310 X0 X0 x
       have j1 := eq11471 X0 X1
       grind)
    | exact resolve eq2310 eq11471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310 eq11471
  have eq52562 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52462
  have eq146812 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op X0 X0) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1125 X0 X2 X0
       have i₂ := eq78 X0 (M.op (M.op (M.op X0 X0) X0) X2) X1
       grind)
    | (have i₁ := eq1125 X0 X2 X0
       have i₂ := eq78 X0 X1 (M.op (M.op (M.op X0 X0) X0) X2)
       grind)
    | exact superpose eq78 eq1125
    | exact resolve eq1125 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq182388 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1161 X0 X1
       have i₂ := eq772 X0 X1
       grind)
    | (have i₁ := eq1161 X1 X1
       have i₂ := eq772 X1 X1
       grind)
    | exact superpose eq772 eq1161
    | exact resolve eq1161 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq1161
  have eq274448 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1))) = (k X0 (σ (M.op X2 (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1))))) ∨ (τ X0) = (M.op (M.op X2 (M.op (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (M.op (τ X0) (τ X0)) X1)) (M.op (M.op (τ X0) (τ X0)) X1))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5120 X0 X1 X2
       have i₂ := eq79 (τ X0) X1
       grind)
    | exact superpose eq79 eq5120
    | (have j0 := eq5120 X0 X1 X2
       grind)
    | exact resolve eq5120 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5120
  have eq274449 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1))) = (k X0 (σ (M.op X2 (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1))))) ∨ (τ X0) = (M.op (M.op X2 (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq274448 X0 X1 X2
       have i₂ := eq79 (τ X0) X1
       grind)
    | exact superpose eq79 eq274448
    | (have j0 := eq274448 X0 X1 X2
       grind)
    | exact resolve eq274448 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq274448
  have eq276441 : ∀ X0 X1 X2 : G, (k X0 (τ (σ (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)))))) = (τ (σ (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)))) ∨ (τ (σ X0)) = (M.op (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (σ (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))))
       have i₂ := eq274449 (σ X0) X1 X2
       grind)
    | exact superpose eq274449 eq28
    | (have j1 := eq274449 (σ X0) X1 X2
       grind)
    | exact resolve eq28 eq274449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq274449
  have eq276731 : ∀ X0 X1 X2 : G, (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)) = (k X0 (τ (σ (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)))))) ∨ (τ (σ X0)) = (M.op (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq276441 X0 X1 X2
       have i₂ := eq10 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))
       grind)
    | exact superpose eq10 eq276441
    | (have j0 := eq276441 X0 X1 X2
       grind)
    | exact resolve eq276441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276441
  have eq276914 : ∀ X0 X1 X2 : G, (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)) = (k X0 (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)))) ∨ (τ (σ X0)) = (M.op (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq276731 X0 X1 X2
       have i₂ := eq10 (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1)))
       grind)
    | exact superpose eq10 eq276731
    | (have j0 := eq276731 X0 X1 X2
       grind)
    | exact resolve eq276731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276731
  have eq277049 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (k X0 (M.op X2 (M.op X0 (M.op (M.op X0 X0) X1)))) ∨ (τ (σ X0)) = (M.op (M.op X2 (M.op (τ (σ X0)) (M.op (M.op (τ (σ X0)) (τ (σ X0))) X1))) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq276914 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq276914
    | (have j0 := eq276914 X0 X1 X2
       grind)
    | exact resolve eq276914 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276914
  have eq277104 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (k X0 (M.op X2 (M.op X0 (M.op (M.op X0 X0) X1)))) ∨ (M.op (M.op X2 (M.op X0 (M.op (M.op X0 X0) X1))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq277049 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277049
    | (have j0 := eq277049 X0 X1 X2
       grind)
    | exact resolve eq277049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277049
  have eq350868 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X0) (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0))) (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52562 (M.op (M.op X0 X1) X0) (M.op x X0)
       have i₂ := eq81 X0 X1 x
       grind)
    | exact superpose eq81 eq52562
    | (have j0 := eq52562 (M.op (M.op X0 X1) X0) X1
       grind)
    | exact resolve eq52562 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52562
  have eq352141 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X0 ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq350868 X0 X1
       have i₂ := eq9 X0 (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq350868
    | (have j0 := eq350868 X0 X1
       grind)
    | exact resolve eq350868 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350868
  have eq352382 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X0 ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq352141 X0 X1
       have i₂ := eq81 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq81 eq352141
    | (have j0 := eq352141 X0 X1
       grind)
    | exact resolve eq352141 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352141
  have eq353019 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq352382 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))))
       have i₂ := eq182388 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq182388 eq352382
    | exact resolve eq352382 eq182388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182388 eq352382
  have eq353393 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq353019 X0
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq353019
    | (have j0 := eq353019 X0
       grind)
    | exact resolve eq353019 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353019
  have eq353469 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq353393 X0
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq353393
    | (have j0 := eq353393 X0
       grind)
    | exact resolve eq353393 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353393
  have eq353539 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq353469 X0
       have j1 := eq1060 X0 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq353469 x
       have r₂ := eq1060 x x x
       grind)
    | exact resolve eq353469 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353469
  have eq354805 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq353539 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq353539
    | exact resolve eq353539 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353539
  have eq355612 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq354805 (σ X0)
       grind)
    | exact superpose eq354805 eq15
    | exact resolve eq15 eq354805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355670 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq354805 (τ X0)
       grind)
    | exact superpose eq354805 eq31
    | exact resolve eq31 eq354805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq355937 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq355670 X0
       have i₂ := eq354805 X0
       grind)
    | exact superpose eq354805 eq355670
    | exact resolve eq355670 eq354805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355670
  have eq355989 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq355612 X0
       have i₂ := eq354805 X0
       grind)
    | exact superpose eq354805 eq355612
    | exact resolve eq355612 eq354805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354805 eq355612
  have eq358119 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq355937 X0
       grind)
    | exact superpose eq355937 eq9
    | exact resolve eq9 eq355937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355937
  have eq358671 : (M.op (σ x) (σ x)) = (σ (M.op (k y x) (k y x))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq355989 (k y x)
       have i₂ := eq16337
       grind)
    | exact superpose eq16337 eq355989
    | exact resolve eq355989 eq16337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16337
  have eq358796 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) x
       have i₂ := eq355989 X0
       grind)
    | exact superpose eq355989 eq52
    | exact resolve eq52 eq355989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358903 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq355989 X0
       grind)
    | exact superpose eq355989 eq9
    | exact resolve eq9 eq355989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359150 : (σ (M.op x x)) = (σ (M.op (k y x) (k y x))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq358671
       have i₂ := eq355989 x
       grind)
    | exact superpose eq355989 eq358671
    | exact resolve eq358671 eq355989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358671
  have eq362293 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X2) (τ X0)) = (τ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq358119 (M.op (M.op X0 X1) X0) X1
       have i₂ := eq81 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq81 eq358119
    | exact resolve eq358119 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358119
  have eq364283 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X1) X0)) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq358796 (M.op (M.op X0 X1) X0) X1
       have i₂ := eq81 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq81 eq358796
    | exact resolve eq358796 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358796
  have eq365130 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq358903 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq358903
    | exact resolve eq358903 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371244 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (τ (M.op (M.op (σ X0) X2) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq362293 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq362293
    | exact resolve eq362293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362293
  have eq386482 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op (M.op X0 X1) X0))) = (σ (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq365130 (M.op (M.op X0 X1) X0) (M.op x (σ X0))
       have i₂ := eq364283 X0 X1 x
       grind)
    | exact superpose eq364283 eq365130
    | exact resolve eq365130 eq364283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364283
  have eq386923 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X2) = (M.op (σ (M.op (M.op X0 X0) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146812 (σ X0) X1 X2
       have i₂ := eq365130 X0 (σ X0)
       grind)
    | exact superpose eq365130 eq146812
    | exact resolve eq146812 eq365130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387910 : ∀ X0 X1 : G, (σ (M.op X0 (M.op (M.op X0 X1) X0))) = (M.op (σ X0) (σ (M.op (M.op X0 X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq386482 X0 X1
       have i₂ := eq1420 X0 X1 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq1420 eq386482
    | exact resolve eq386482 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420 eq386482
  have eq414260 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X0) X3) = (M.op (τ (M.op (M.op (σ X0) X1) (σ X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq146812 X0 X2 X3
       have i₂ := eq371244 X0 X0 X1
       grind)
    | exact superpose eq371244 eq146812
    | exact resolve eq146812 eq371244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146812
  have eq414648 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) X0) (τ (M.op (M.op (σ X0) X1) (σ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 X2 (M.op X0 x)
       have i₂ := eq371244 X0 x X1
       grind)
    | exact superpose eq371244 eq81
    | exact resolve eq81 eq371244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq371244
  have eq1066625 : ∀ X0 X1 : G, (M.op (k y x) (k y x)) = (M.op (M.op (M.op (M.op (k y x) (k y x)) X0) (M.op (k y x) (k y x))) (τ (M.op (M.op (σ (M.op x x)) X1) (σ (M.op x x))))) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq414648 (M.op (k y x) (k y x)) X1 x
       have i₂ := eq359150
       grind)
    | exact superpose eq359150 eq414648
    | exact resolve eq414648 eq359150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414648
  have eq1066663 : ∀ X0 : G, (M.op (k y x) (k y x)) = (M.op (M.op (M.op (M.op (k y x) (k y x)) X0) (M.op (k y x) (k y x))) (τ (σ x))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1066625 X0 x
       have i₂ := eq358903 x x
       grind)
    | exact superpose eq358903 eq1066625
    | exact resolve eq1066625 eq358903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066625
  have eq1066907 : ∀ X0 : G, (M.op (k y x) (k y x)) = (M.op (M.op (M.op (M.op (k y x) (k y x)) X0) (M.op (k y x) (k y x))) x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1066663 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1066663
    | exact resolve eq1066663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066663
  have eq1067000 : (M.op (k y x) (k y x)) = (M.op (k y x) x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1066907 x
       have i₂ := eq9 (k y x) x (k y x)
       grind)
    | exact superpose eq9 eq1066907
    | exact resolve eq1066907 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066907
  have eq1465303 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op (σ (M.op x x)) X2) (σ (M.op x x)))) X1) = (M.op (M.op (M.op (M.op (k y x) (k y x)) X0) (M.op (k y x) (k y x))) X1) ∨ x = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq414260 (M.op (k y x) (k y x)) X1 X2 x
       have i₂ := eq359150
       grind)
    | exact superpose eq359150 eq414260
    | exact resolve eq414260 eq359150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359150 eq414260
  have eq1469221 : ∀ X1 X2 : G, (M.op (k y x) X1) = (M.op (τ (M.op (M.op (σ (M.op x x)) X2) (σ (M.op x x)))) X1) ∨ x = (M.op y x) := by
    intro X1 X2
    first
    | (have i₁ := eq1465303 x X1 X2
       have i₂ := eq9 (k y x) x (k y x)
       grind)
    | exact superpose eq9 eq1465303
    | exact resolve eq1465303 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465303
  have eq1470450 : ∀ X1 : G, (M.op (k y x) X1) = (M.op (τ (σ x)) X1) ∨ x = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq1469221 X1 x
       have i₂ := eq358903 x x
       grind)
    | exact superpose eq358903 eq1469221
    | exact resolve eq1469221 eq358903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358903 eq1469221
  have eq1471047 : ∀ X1 : G, (M.op x X1) = (M.op (k y x) X1) ∨ x = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq1470450 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1470450
    | exact resolve eq1470450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470450
  have eq1991952 : (M.op (k y x) x) = (M.op x (k y x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1471047 (k y x)
       have i₂ := eq1067000
       grind)
    | exact superpose eq1067000 eq1471047
    | exact resolve eq1471047 eq1067000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067000 eq1471047
  have eq1992560 : (M.op (k y x) x) = (M.op x (k y x)) ∨ x = (M.op y x) := by grind
  clear eq1991952
  have eq1992650 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) (M.op x (k y x))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 (k y x)
       have i₂ := eq1992560
       grind)
    | exact superpose eq1992560 eq9
    | exact resolve eq9 eq1992560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992560
  have eq2412276 : ∀ X0 X1 : G, x ≠ (M.op (M.op (M.op (M.op x x) X0) (M.op (M.op x x) X0)) x) ∨ (k X1 x) = (M.op X1 x) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq1060 (M.op (M.op x x) X0) (M.op x (k y x)) x
       have i₂ := eq1992650 X0
       grind)
    | exact superpose eq1992650 eq1060
    | exact resolve eq1060 eq1992650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060 eq1992650
  have eq2412645 : ∀ X1 : G, x ≠ (M.op x x) ∨ (k X1 x) = (M.op X1 x) ∨ x = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq2412276 x X1
       have i₂ := eq1088 x x x
       grind)
    | exact superpose eq1088 eq2412276
    | (have j0 := eq2412276 x X1
       grind)
    | exact resolve eq2412276 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088 eq2412276
  have eq2412706 : ∀ X1 : G, (k X1 x) = (M.op X1 x) ∨ x = (M.op y x) := by
    intro X1
    first
    | (have j0 := eq2412645 X1
       grind)
    | (have r₁ := eq2412645 X1
       have r₂ := eq21303
       grind)
    | exact resolve eq2412645 eq21303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21303 eq2412645
  have eq2413569 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16249
       have i₂ := eq2412706 y
       grind)
    | exact superpose eq2412706 eq16249
    | exact resolve eq16249 eq2412706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16249 eq2412706
  have eq2413908 : x = (M.op y x) := by grind
  clear eq2413569
  have eq2414295 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq2413908
       grind)
    | exact superpose eq2413908 eq9
    | exact resolve eq9 eq2413908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2414299 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq78 y x X0
       have i₂ := eq2413908
       grind)
    | exact superpose eq2413908 eq78
    | exact resolve eq78 eq2413908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2414321 : ∀ X0 : G, x = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq750 y x x
       have i₂ := eq2413908
       grind)
    | exact superpose eq2413908 eq750
    | exact resolve eq750 eq2413908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq2414327 : (M.op y y) = (M.op (M.op (M.op x x) (M.op x x)) y) := by
    first
    | (have i₁ := eq1046 y x
       have i₂ := eq2413908
       grind)
    | exact superpose eq2413908 eq1046
    | exact resolve eq1046 eq2413908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq2414946 : ∀ X0 : G, y = (M.op (M.op X0 x) y) ∨ x = (k y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq277104 y x x
       have i₂ := eq2414321 (M.op y y)
       grind)
    | exact superpose eq2414321 eq277104
    | exact resolve eq277104 eq2414321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277104 eq2414321
  have eq2499151 : y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq2414946 (M.op (M.op x x) x)
       have i₂ := eq2414295 x
       grind)
    | exact superpose eq2414295 eq2414946
    | exact resolve eq2414946 eq2414295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414946
  have eq2500847 : ∀ X0 : G, x ≠ (M.op y x) ∨ (k X0 (M.op y x)) = (M.op X0 (M.op y x)) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq571 x y x
       have i₂ := eq2499151
       grind)
    | exact superpose eq2499151 eq571
    | exact resolve eq571 eq2499151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq2499151
  have eq2501312 : ∀ X0 : G, (k X0 (M.op y x)) = (M.op X0 (M.op y x)) ∨ x = (k y x) := by
    intro X0
    first
    | (have j0 := eq2500847 X0
       grind)
    | (have r₁ := eq2500847 X0
       have r₂ := eq2413908
       grind)
    | exact resolve eq2500847 eq2413908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500847
  have eq2501402 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq2501312 X0
       have i₂ := eq2413908
       grind)
    | exact superpose eq2413908 eq2501312
    | exact resolve eq2501312 eq2413908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501312
  have eq2523151 : x ≠ (M.op y x) ∨ x = (k y x) := by grind
  clear eq2501402
  have eq2523156 : x = (k y x) := by
    first
    | (have r₁ := eq2523151
       have r₂ := eq2413908
       grind)
    | exact resolve eq2523151 eq2413908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413908 eq2523151
  have eq2523398 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq488 y x X0
       have i₂ := eq2523156
       grind)
    | exact superpose eq2523156 eq488
    | (have j0 := eq488 y x x
       grind)
    | exact resolve eq488 eq2523156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq2523588 : (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2523398 x
       have i₂ := eq365130 y x
       grind)
    | exact superpose eq365130 eq2523398
    | exact resolve eq2523398 eq365130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523398
  have eq2523614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2523588
       have i₂ := eq2414299 y
       grind)
    | exact superpose eq2414299 eq2523588
    | exact resolve eq2523588 eq2414299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414299 eq2523588
  have eq2523625 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2523614
       have r₂ := eq16
       grind)
    | exact resolve eq2523614 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523614
  have eq2523773 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2523625
       grind)
    | exact superpose eq2523625 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2523625
       grind)
    | exact resolve eq13 eq2523625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2524082 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by grind
  clear eq2523773
  have eq2524322 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2524082
       have i₂ := eq355989 x
       grind)
    | exact superpose eq355989 eq2524082
    | exact resolve eq2524082 eq355989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524082
  have eq2524511 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2524322
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2524322
    | exact resolve eq2524322 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524322
  have eq2524606 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2524511
       have i₂ := eq355989 x
       grind)
    | exact superpose eq355989 eq2524511
    | exact resolve eq2524511 eq355989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524511
  have eq2524648 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2524606
       have i₂ := eq2523156
       grind)
    | exact superpose eq2523156 eq2524606
    | exact resolve eq2524606 eq2523156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523156 eq2524606
  have eq2524649 : (σ x) = (σ (M.op x x)) := by grind
  clear eq2524648
  have eq2524786 : (τ (σ x)) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2524649
       grind)
    | exact superpose eq2524649 eq10
    | exact resolve eq10 eq2524649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524649
  have eq2526225 : x = (M.op x x) := by
    first
    | (have i₁ := eq2524786
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2524786
    | exact resolve eq2524786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524786
  have eq2526663 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq2414295 X0
       have i₂ := eq2526225
       grind)
    | exact superpose eq2526225 eq2414295
    | exact resolve eq2414295 eq2526225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414295
  have eq2526665 : (M.op y y) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq2414327
       have i₂ := eq2526225
       grind)
    | exact superpose eq2526225 eq2414327
    | exact resolve eq2414327 eq2526225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414327
  have eq2526720 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq52 x x
       have i₂ := eq2526225
       grind)
    | exact superpose eq2526225 eq52
    | exact resolve eq52 eq2526225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2527631 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2526665
       have i₂ := eq2526225
       grind)
    | exact superpose eq2526225 eq2526665
    | exact resolve eq2526665 eq2526225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526225 eq2526665
  have eq2566236 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2))) = (M.op (M.op X0 (M.op (M.op X0 X1) X0)) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12990 X0 X1 X2 x
       have i₂ := eq13149 X0 X1 (M.op X0 X2) x
       grind)
    | exact superpose eq13149 eq12990
    | exact resolve eq12990 eq13149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12990 eq13149
  have eq2572512 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (M.op (σ x) X0) (σ x)) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (σ x) X0) (σ x))) (M.op (M.op (M.op (σ x) X0) (σ x)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2566236 (σ x) x (σ y)
       have i₂ := eq2523625
       grind)
    | exact superpose eq2523625 eq2566236
    | exact resolve eq2566236 eq2523625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566236
  have eq2574317 : ∀ X0 : G, (M.op (σ y) (M.op (σ (M.op (M.op x x) x)) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (σ x) X0) (σ x))) (M.op (σ (M.op (M.op x x) x)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2572512 x
       have i₂ := eq386923 x x (σ y)
       grind)
    | exact superpose eq386923 eq2572512
    | exact resolve eq2572512 eq386923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386923 eq2572512
  have eq2575239 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (σ x) X0) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2574317 X0
       have i₂ := eq2526663 x
       grind)
    | exact superpose eq2526663 eq2574317
    | exact resolve eq2574317 eq2526663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526663 eq2574317
  have eq2575668 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) X0) (σ x))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2575239 X0
       have i₂ := eq2523625
       grind)
    | exact superpose eq2523625 eq2575239
    | exact resolve eq2575239 eq2523625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523625 eq2575239
  have eq2575902 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ (M.op (M.op x x) x))) (σ y)) := by
    first
    | (have i₁ := eq2575668 x
       have i₂ := eq365130 x x
       grind)
    | exact superpose eq365130 eq2575668
    | exact resolve eq2575668 eq365130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365130 eq2575668
  have eq2575999 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x (M.op (M.op x x) x))) (σ y)) := by
    first
    | (have i₁ := eq2575902
       have i₂ := eq387910 x x
       grind)
    | exact superpose eq387910 eq2575902
    | exact resolve eq2575902 eq387910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387910 eq2575902
  have eq2576036 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2575999
       have i₂ := eq2526720 (M.op x x)
       grind)
    | exact superpose eq2526720 eq2575999
    | exact resolve eq2575999 eq2526720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526720 eq2575999
  have eq2576052 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2576036
       have i₂ := eq355989 y
       grind)
    | exact superpose eq355989 eq2576036
    | exact resolve eq2576036 eq355989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355989 eq2576036
  have eq2576060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2576052
       have i₂ := eq2527631
       grind)
    | exact superpose eq2527631 eq2576052
    | exact resolve eq2576052 eq2527631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527631 eq2576052
  have eq2576063 : False := by grind
  exact eq2576063

/-- `Equation2062`: `x = ((x ◇ y) ◇ y) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_pyy_pyx_y_pyx_Equation2062 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2062 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2062.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op x X0)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X2 (M.op X0 x)
       have i₂ := eq14 X0 X1 x
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
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
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
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq36
  have eq103 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq92
    | (have j1 := eq86 y x
       grind)
    | exact resolve eq92 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq236 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq242 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 X1 (M.op X0 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 X0) X0 X0
       have i₂ := eq56 X0 X0 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq600 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq595 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq595
    | exact resolve eq595 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq123 eq86
    | (have j0 := eq86 (σ y) (σ x)
       grind)
    | exact resolve eq86 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq764
    | exact resolve eq764 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq768 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq765
       have r₂ := eq27
       grind)
    | exact resolve eq765 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq770 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq768
    | exact resolve eq768 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq772 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq770 eq78
    | (have r₁ := eq78
       have r₂ := eq770
       grind)
    | exact resolve eq78 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq782 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq770 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq784 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq772
  have eq1250 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq784 eq782
    | (have j0 := eq782 (σ y)
       grind)
    | (have r₁ := eq782 (σ y)
       have r₂ := eq784
       grind)
    | exact resolve eq782 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq784
  have eq1251 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1250
  have eq1252 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1251
  have eq1256 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1252
    | exact resolve eq1252 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq123 eq1256
    | exact resolve eq1256 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1256 eq123
    | exact resolve eq123 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq1256
  have eq1266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1262
  have eq1267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1260
  have eq1268 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1266
       have r₂ := eq27
       grind)
    | exact resolve eq1266 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq1269 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1267
       have r₂ := eq27
       grind)
    | exact resolve eq1267 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1299 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1269
       grind)
    | exact superpose eq1269 eq72
    | exact resolve eq72 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1314 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq1299
    | exact resolve eq1299 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq1321 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1314 eq55
    | exact resolve eq55 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1322 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1314 eq51
    | exact resolve eq51 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1323 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1314 eq14
    | exact resolve eq14 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1314 eq14
    | exact resolve eq14 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1331 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1314 eq600
    | exact resolve eq600 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq1340 : (τ (σ x)) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1268 eq103
    | exact resolve eq103 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq1268
  have eq1346 : (M.op x y) = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq28 eq1340
    | exact resolve eq1340 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1340
  have eq1387 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq1346
       grind)
    | exact superpose eq1346 eq77
    | (have r₁ := eq77
       have r₂ := eq1346
       grind)
    | exact resolve eq77 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1388 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1346
       grind)
    | exact superpose eq1346 eq72
    | exact resolve eq72 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1402 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (k y x) := by grind
  clear eq1387
  have eq1403 : (M.op x y) = (M.op y y) ∨ x = (k y x) := by grind
  clear eq1402
  have eq1404 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq1388
    | exact resolve eq1388 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1428 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1322 eq242
    | exact resolve eq242 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq1322
  have eq1439 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1331 eq14
    | exact resolve eq14 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq1466 : ∀ X0 : G, y = (M.op (M.op (M.op x y) y) (M.op y X0)) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq1403
       grind)
    | exact superpose eq1403 eq14
    | exact resolve eq14 eq1403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1607 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ x)) X0) X0) = (M.op (M.op (M.op (σ (M.op x y)) (σ x)) (σ x)) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1321 eq591
    | exact resolve eq591 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1621 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1314 eq591
    | exact resolve eq591 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1663 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ x)) X0) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1607 X0
       have i₂ := eq14 sF1 sF2 sF2
       grind)
    | exact superpose eq14 eq1607
    | exact resolve eq1607 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq1753 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1439 eq1324
    | exact resolve eq1324 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1777 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq1753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq2757 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1323 eq1663
    | exact resolve eq1663 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323 eq1663
  have eq2790 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq2757 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757
  have eq3458 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1777 x
       have i₂ := eq591 sF1 x x
       grind)
    | exact superpose eq591 eq1777
    | exact resolve eq1777 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq1777
  have eq7754 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1621 eq1428
    | exact resolve eq1428 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428 eq1621
  have eq7766 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq7754 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7754
  have eq7868 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1439 eq7766
    | exact resolve eq7766 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq7872 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2790 eq7766
    | exact resolve eq7766 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790 eq7766
  have eq7955 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq7872 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7872
  have eq7958 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq7868 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7868
  have eq8910 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq7958 eq3458
    | exact resolve eq3458 eq7958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458 eq7958
  have eq8936 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq8910 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8910
  have eq9750 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7955 eq8936
    | exact resolve eq8936 eq7955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7955 eq8936
  have eq9787 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq9750
  have eq14519 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1466 y
       have i₂ := eq1403
       grind)
    | exact superpose eq1403 eq1466
    | exact resolve eq1466 eq1403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403 eq1466
  have eq14550 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ x = (k y x) := by grind
  clear eq14519
  have eq14553 : x = (k y x) ∨ x = y := by
    first
    | exact superpose eq236 eq14550
    | exact resolve eq14550 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14550
  have eq14555 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq14553
       grind)
    | exact superpose eq14553 eq92
    | exact resolve eq92 eq14553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq14559 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq86 y x
       have i₂ := eq14553
       grind)
    | exact superpose eq14553 eq86
    | (have j0 := eq86 y x
       grind)
    | exact resolve eq86 eq14553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14553
  have eq14560 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq14559
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14559
    | exact resolve eq14559 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14559
  have eq14564 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14555
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14555
    | exact resolve eq14555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14555
  have eq14566 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14560
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14560
    | exact resolve eq14560 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14560
  have eq14591 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq14564 eq86
    | (have j0 := eq86 (σ y) (σ x)
       grind)
    | exact resolve eq86 eq14564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq14564
  have eq14592 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq14591
    | exact resolve eq14591 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14591
  have eq14595 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq14592
    | exact resolve eq14592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14592
  have eq14757 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq14566
       grind)
    | exact superpose eq14566 eq72
    | exact resolve eq72 eq14566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14566
  have eq14802 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq14757
    | exact resolve eq14757 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14757
  have eq14806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq14595 eq1314
    | exact resolve eq1314 eq14595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14872 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq14806
       have r₂ := eq27
       grind)
    | exact resolve eq14806 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14806
  have eq15129 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq14872 eq9787
    | exact resolve eq9787 eq14872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9787
  have eq15134 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq15129
  have eq15181 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq26 eq15134
    | exact resolve eq15134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15134
  have eq15605 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14802 eq14595
    | exact resolve eq14595 eq14802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq15605
  have eq15669 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15666
       have r₂ := eq27
       grind)
    | exact resolve eq15666 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15666
  have eq15672 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq15669 eq27
    | exact resolve eq27 eq15669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15669
  have eq16189 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq14872 eq15181
    | exact resolve eq15181 eq14872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14872 eq15181
  have eq16221 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq16189
  have eq16488 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq16221 eq1314
    | exact resolve eq1314 eq16221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16491 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq16221 eq14802
    | exact resolve eq14802 eq16221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14802 eq16221
  have eq16576 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16491
  have eq16579 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq16488
  have eq16585 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq16576
       have r₂ := eq15672
       grind)
    | exact resolve eq16576 eq15672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15672 eq16576
  have eq16675 : x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq16585 eq236
    | exact resolve eq236 eq16585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq16746 : x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq16675
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16675
    | exact resolve eq16675 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16675
  have eq17538 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq16585 eq16746
    | exact resolve eq16746 eq16585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16585 eq16746
  have eq17581 : x = (M.op x x) ∨ x = y := by grind
  clear eq17538
  have eq18296 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq17581
       grind)
    | exact superpose eq17581 eq72
    | exact resolve eq72 eq17581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq17581
  have eq18356 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq18296
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18296
    | exact resolve eq18296 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18296
  have eq18368 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18356 eq14595
    | exact resolve eq14595 eq18356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14595 eq18356
  have eq18436 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq18368
  have eq18445 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq18436 eq27
    | exact resolve eq27 eq18436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18436
  have eq18570 : x = y := by
    first
    | (have r₁ := eq18445
       have r₂ := eq16579
       grind)
    | exact resolve eq18445 eq16579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16579 eq18445
  have eq18578 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18570
       grind)
    | exact superpose eq18570 eq18
    | exact resolve eq18 eq18570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq18579 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq18570
       grind)
    | exact superpose eq18570 eq24
    | exact resolve eq24 eq18570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq18625 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18579
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18579
    | exact resolve eq18579 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18579
  have eq18628 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18625 eq26
    | exact resolve eq26 eq18625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq18625
  have eq18770 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18628 eq71
    | exact resolve eq71 eq18628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq18772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18628 eq1314
    | exact resolve eq1314 eq18628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq18773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq18628 eq1404
    | exact resolve eq1404 eq18628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404 eq18628
  have eq18847 : x = (k y x) := by
    first
    | (have r₁ := eq18773
       have r₂ := eq27
       grind)
    | exact resolve eq18773 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18773
  have eq18848 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq18772
       have r₂ := eq27
       grind)
    | exact resolve eq18772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18772
  have eq18850 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18770
       have i₂ := eq18578
       grind)
    | exact superpose eq18578 eq18770
    | exact resolve eq18770 eq18578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18770
  have eq18853 : x = (k x x) := by
    first
    | (have i₁ := eq18847
       have i₂ := eq18570
       grind)
    | exact superpose eq18570 eq18847
    | exact resolve eq18847 eq18570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18570 eq18847
  have eq18855 : x = (M.op x x) := by
    first
    | (have i₁ := eq18853
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq18853
    | exact resolve eq18853 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq18853
  have eq18857 : x = (M.op x y) := by
    first
    | (have i₁ := eq18855
       have i₂ := eq18578
       grind)
    | exact superpose eq18578 eq18855
    | exact resolve eq18855 eq18578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18578 eq18855
  have eq20499 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18857 eq18850
    | exact resolve eq18850 eq18857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18850 eq18857
  have eq20513 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20499 eq15
    | exact resolve eq15 eq20499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20499
  have eq20563 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20513
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20513
    | exact resolve eq20513 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20513
  have eq20579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18848 eq20563
    | exact resolve eq20563 eq18848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18848 eq20563
  have eq20593 : False := by grind
  exact eq20593

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pyy_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X1 X1) X2
       have i₂ := eq9 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X0 X0)) = (M.op X3 X1) ∨ (M.op X3 X1) = (k X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq143 X1 X3
       have i₂ := eq30 X1 X2 X0
       grind)
    | (have i₁ := eq143 (M.op X2 X2) X1
       have i₂ := eq30 X0 X2 X2
       grind)
    | exact superpose eq30 eq143
    | (have j0 := eq143 X1 X3
       grind)
    | exact resolve eq143 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq143 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq143 X0 X1
       grind)
    | exact superpose eq143 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq143 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq143 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq143 X1 X1
       grind)
    | exact resolve eq13 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq213 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq215 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq213 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq213 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq369 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X0 X0)) = (k X3 X1) ∨ (k X3 X1) = (M.op X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq215 X3 X1
       have i₂ := eq30 X1 X2 X0
       grind)
    | (have i₁ := eq215 X0 (M.op X2 X2)
       have i₂ := eq30 X0 X2 X2
       grind)
    | exact superpose eq30 eq215
    | (have j0 := eq215 X3 X1
       grind)
    | exact resolve eq215 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq215
  have eq8326 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) ≠ (M.op (M.op X2 X2) (M.op X3 X3)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq369 X0 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq8328 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq8326 X0 X1 x x
       have j1 := eq189 X0 X0 x X1
       grind)
    | (have r₁ := eq8326 (M.op X0 X0) (M.op x x) x x
       have r₂ := eq189 X0 (M.op x x) x (M.op x x)
       grind)
    | (have r₁ := eq8326 X1 x x X0
       have r₂ := eq189 X0 X1 x x
       grind)
    | exact resolve eq8326 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq8326
  have eq8394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq8328 (σ X0) (σ X1)
       grind)
    | exact superpose eq8328 eq15
    | exact resolve eq15 eq8328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8405 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8394 X0 X1
       have i₂ := eq8328 X0 X1
       grind)
    | exact superpose eq8328 eq8394
    | exact resolve eq8394 eq8328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8328 eq8394
  have eq8812 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8405 y x
       grind)
    | exact superpose eq8405 eq16
    | (have r₁ := eq16
       have r₂ := eq8405 y x
       grind)
    | exact resolve eq16 eq8405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8405
  have eq8833 : False := by grind
  exact eq8833

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_y_Equation2132 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law2132 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
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
  have eq118 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq25 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq25 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq126 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq13 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq126 (σ X0) (σ X1)
       grind)
    | exact superpose eq126 eq15
    | (have j1 := eq126 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq126 X0 X1
       grind)
    | exact superpose eq126 eq141
    | (have j0 := eq141 X0 X1
       have j1 := eq126 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq141 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq141
  have eq242 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq118 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq118 (σ X1) X0
       grind)
    | exact superpose eq118 eq22
    | exact resolve eq22 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq118
  have eq1529 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq143 x y
       grind)
    | exact superpose eq143 eq16
    | (have j1 := eq143 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq143 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq143 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq143 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq1533 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1529
  have eq3049 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1533
       grind)
    | exact superpose eq1533 eq10
    | exact resolve eq10 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq3072 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3049
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3049
    | exact resolve eq3049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049
  have eq3073 : x = y := by grind
  clear eq3072
  have eq3516 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3073
       grind)
    | exact superpose eq3073 eq16
    | exact resolve eq16 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073
  have eq3517 : False := by grind
  exact eq3517

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq63 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq418 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 (σ X1)) = (σ (M.op (τ X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq418 X2 X1
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq418 X2 X1
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq418
    | (have j0 := eq418 X2 X1
       grind)
    | (have r₁ := eq418 X0 (M.op X0 X0)
       have r₂ := eq69 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq418 X0 (M.op X1 X1)
       have r₂ := eq69 (M.op X1 X1) X1
       grind)
    | exact resolve eq418 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1618 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq1625 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1618 X0 X1
       have j1 := eq928 X0 X1 X0
       grind)
    | (have r₁ := eq1618 X0 X1
       have r₂ := eq928 (τ X0) X1 x
       grind)
    | (have r₁ := eq1618 X0 (M.op X0 X0)
       have r₂ := eq928 X0 (M.op (τ X0) (τ X0)) x
       grind)
    | (have r₁ := eq1618 X0 X1
       have r₂ := eq928 X1 X1 x
       grind)
    | exact resolve eq1618 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq1618
  have eq1648 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1625 X0 X1
       have j1 := eq418 X0 X1
       grind)
    | (have r₁ := eq1625 X0 X1
       have r₂ := eq418 X0 X1
       grind)
    | exact resolve eq1625 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq1625
  have eq1650 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1648 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1648
    | exact resolve eq1648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq5917 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq1650 X0 X1
       grind)
    | exact superpose eq1650 eq23
    | exact resolve eq23 eq1650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq5965 : ∀ X0 X1 : G, (M.op X0 X1) = (k (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5917 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5917
    | exact resolve eq5917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5917
  have eq6004 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5965 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5965
    | exact resolve eq5965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5965
  have eq6109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1650 X0 X1
       have i₂ := eq6004 (σ X0) (σ X1)
       grind)
    | exact superpose eq6004 eq1650
    | exact resolve eq1650 eq6004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650 eq6004
  have eq7985 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6109 x y
       grind)
    | exact superpose eq6109 eq16
    | (have r₁ := eq16
       have r₂ := eq6109 x y
       grind)
    | exact resolve eq16 eq6109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6109
  have eq8055 : False := by grind
  exact eq8055

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq178 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (σ x) = (M.op (M.op (k X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq178
    | exact resolve eq178 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq182 : ∀ X0 : G, x = (M.op (M.op (k X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (k X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq186 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X2 (M.op (M.op X1 X1) (k X2 X2))
       have i₂ := eq16 X0 X1 (k X2 X2)
       grind)
    | exact superpose eq16 eq183
    | exact resolve eq183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq647
    | exact resolve eq647 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X1 x x
       have i₂ := eq652 X0 x x
       grind)
    | (have i₁ := eq652 X0 X1 X1
       have i₂ := eq652 (k X1 X1) X1 x
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X0 X2
       grind)
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X2 X0
       grind)
    | exact superpose eq698 eq186
    | exact resolve eq186 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X1 x (k X1 X1)
       have i₂ := eq698 X0 (M.op (k X1 X1) x)
       grind)
    | (have i₁ := eq186 X1 x (k X1 X1)
       have i₂ := eq698 (M.op (k X1 X1) x) X0
       grind)
    | exact superpose eq698 eq186
    | exact resolve eq186 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq773 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq757
    | exact resolve eq757 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq806 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X1 x (k X1 X1)
       have i₂ := eq762 (M.op (k X1 X1) x) X0
       grind)
    | exact superpose eq762 eq186
    | exact resolve eq186 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq762
  have eq1263 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ y = (k x y) := by
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
  have eq1264 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1266 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1264
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1264
    | exact resolve eq1264 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1267 : (M.op x y) ≠ (k x x) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq1263
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1263
    | exact resolve eq1263 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1292 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq1293 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1350 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1293
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1293
    | exact resolve eq1293 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1351 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1292
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1292
    | exact resolve eq1292 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq8595 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1351
       grind)
    | exact superpose eq1351 eq40
    | exact resolve eq40 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1351
  have eq8596 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq8595
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8595
    | exact resolve eq8595 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8595
  have eq8598 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq8596
    | exact resolve eq8596 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8596
  have eq19638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq8598 eq1350
    | exact resolve eq1350 eq8598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19648 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq19638
       have r₂ := eq27
       grind)
    | exact resolve eq19638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19638
  have eq19654 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq19648 eq1266
    | (have r₁ := eq1266
       have r₂ := eq19648
       grind)
    | exact resolve eq1266 eq19648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq19648
  have eq19846 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq19654
  have eq19847 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq19846
  have eq23192 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq19847 eq8598
    | exact resolve eq8598 eq19847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8598
  have eq23195 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq19847 eq90
    | exact resolve eq90 eq19847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq19847
  have eq23200 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23192
  have eq23205 : y = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq23195
    | exact resolve eq23195 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23195
  have eq23208 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq23205
       have r₂ := eq1267
       grind)
    | exact resolve eq23205 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267 eq23205
  have eq23213 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq23208
       grind)
    | exact superpose eq23208 eq35
    | exact resolve eq35 eq23208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq23208
  have eq23221 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23213
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23213
    | exact resolve eq23213 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23213
  have eq23227 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23221 eq1350
    | exact resolve eq1350 eq23221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq23221
  have eq23234 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23227
  have eq23442 : x = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq23200
       grind)
    | exact superpose eq23200 eq182
    | exact resolve eq182 eq23200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq23484 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (k X1 X1)) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq773 X1 x X0
       have i₂ := eq23200
       grind)
    | exact superpose eq23200 eq773
    | exact resolve eq773 eq23200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23486 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq806 X0 x
       have i₂ := eq23200
       grind)
    | exact superpose eq23200 eq806
    | exact resolve eq806 eq23200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23200
  have eq23718 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq23486 eq23484
    | exact resolve eq23484 eq23486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23484 eq23486
  have eq27326 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23234 eq181
    | exact resolve eq181 eq23234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq27369 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (k X1 X1)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq23234 eq773
    | exact resolve eq773 eq23234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq27371 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23234 eq806
    | exact resolve eq806 eq23234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq23234
  have eq27595 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27371 eq27369
    | exact resolve eq27369 eq27371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27369 eq27371
  have eq34486 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23718 eq23442
    | exact resolve eq23442 eq23718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23442 eq23718
  have eq34494 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq34486
  have eq46160 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27595 eq27326
    | exact resolve eq27326 eq27595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27326 eq27595
  have eq46168 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq46160
  have eq46177 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq46168 eq27
    | exact resolve eq27 eq46168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46168
  have eq46237 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq46177
       have r₂ := eq34494
       grind)
    | exact resolve eq46177 eq34494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34494 eq46177
  have eq46247 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq46237 eq31
    | exact resolve eq31 eq46237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq46237
  have eq46292 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq46247
    | exact resolve eq46247 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq46247
  have eq46293 : x = y := by grind
  clear eq46292
  have eq46307 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq46293
       grind)
    | exact superpose eq46293 eq18
    | exact resolve eq18 eq46293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq46308 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq46293
       grind)
    | exact superpose eq46293 eq24
    | exact resolve eq24 eq46293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq46293
  have eq46328 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq46308
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46308
    | exact resolve eq46308 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46308
  have eq46329 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq46307
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq46307
    | exact resolve eq46307 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46307
  have eq46331 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq46328 eq26
    | exact resolve eq26 eq46328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq46328
  have eq46372 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq46331
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq46331
    | exact resolve eq46331 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq46331
  have eq46385 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq46329
       grind)
    | exact superpose eq46329 eq39
    | exact resolve eq39 eq46329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq46329
  have eq46719 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq46385
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46385
    | exact resolve eq46385 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq46385
  have eq46802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46372 eq46719
    | exact resolve eq46719 eq46372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46372 eq46719
  have eq46861 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq46802
    | exact resolve eq46802 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq46802
  have eq46903 : False := by grind
  exact eq46903

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pyy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq125 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq119 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq119 X0 X1
       grind)
    | exact resolve eq13 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq125 (σ X1) (σ X0)
       grind)
    | exact superpose eq125 eq15
    | (have j1 := eq125 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 X1
       have i₂ := eq125 X1 X0
       grind)
    | exact superpose eq125 eq134
    | (have j0 := eq134 X0 X1
       have j1 := eq125 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq134 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq134
  have eq347 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq119 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq119 (σ X1) X0
       grind)
    | exact superpose eq119 eq22
    | exact resolve eq22 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq119
  have eq2201 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq170 x y
       grind)
    | exact superpose eq170 eq16
    | (have j1 := eq170 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq170 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq170 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq170 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq2216 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2201
  have eq6535 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2216
       grind)
    | exact superpose eq2216 eq10
    | exact resolve eq10 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq6548 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6535
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6535
    | exact resolve eq6535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq6549 : x = y := by grind
  clear eq6548
  have eq16114 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6549
       grind)
    | exact superpose eq6549 eq16
    | exact resolve eq16 eq6549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6549
  have eq16115 : False := by grind
  exact eq16115

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_x_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq100 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq100 (σ X1) (σ X0)
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq100 X1 X0
       grind)
    | exact superpose eq100 eq109
    | (have j0 := eq109 X0 X1
       have j1 := eq100 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq109 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq109
  have eq317 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq95 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq95 (σ X1) X0
       grind)
    | exact superpose eq95 eq22
    | exact resolve eq22 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq95
  have eq2044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq145 x y
       grind)
    | exact superpose eq145 eq16
    | (have j1 := eq145 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq2057 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2044
  have eq7787 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2057
       grind)
    | exact superpose eq2057 eq10
    | exact resolve eq10 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq7800 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7787
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7787
    | exact resolve eq7787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7787
  have eq7801 : x = y := by grind
  clear eq7800
  have eq17741 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7801
       grind)
    | exact superpose eq7801 eq16
    | exact resolve eq16 eq7801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7801
  have eq17742 : False := by grind
  exact eq17742
